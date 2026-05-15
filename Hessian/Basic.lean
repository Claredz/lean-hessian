import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Topology
open ContinuousLinearMap

set_option linter.unusedSectionVars false

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `x₀` 是 `f` 的局部极小点：存在 `ε > 0` 使得对 `dist y x₀ < ε` 的 `y` 有 `f x₀ ≤ f y`。 -/
def LocalMinimumAt (f : E → ℝ) (x₀ : E) : Prop :=
  ∃ ε > 0, ∀ y : E, dist y x₀ < ε → f x₀ ≤ f y

/-- Hessian 算子：梯度函数 `y ↦ ∇f(y)` 在 `x` 处的 Fréchet 导数。
`HessianOp f x` 是连续线性映射 `E →L[ℝ] E`，数学上 `HessianOp f x = D(∇f)(x)`。 -/
noncomputable def HessianOp (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (fun y => gradient f y) x

/-- `A` 是半正定的：对所有 `v` 有 `0 ≤ ⟨A v, v⟩`。 -/
def PosSemidefOp (A : E →L[ℝ] E) : Prop :=
  ∀ v : E, 0 ≤ inner ℝ (A v) v

/-- `f` 在 `x` 处的 Hessian 是半正定的。 -/
def HessianPosSemidefAt (f : E → ℝ) (x : E) : Prop :=
  PosSemidefOp (HessianOp f x)

/-- **局部极小值的二阶必要条件。**
若 `x₀` 是 `f` 的局部极小点，`∇f(x₀) = 0`，`f` 在 `x₀` 附近可微，
`∇f` 在 `x₀` 处可微且导数为 `A`，则 `A` 是半正定的。

证明思路（化归到一维）：
1. 固定方向 `v`，定义 `g(t) = f(x₀ + t • v)`
2. 由 `hgrad` 和 `hHess` 经链式法则得 `g'(0) = 0`，`g''(0) = ⟨A v, v⟩`
3. 由 `hmin` 得 `g` 在 `0` 处有局部极小值
4. 由一维二阶必要条件得 `0 ≤ g''(0) = ⟨A v, v⟩`
5. 由 `v` 的任意性得 `A ≽ 0`

当前状态：该定理留作 `sorry`。所有辅助引理均已完成证明。 -/
theorem second_order_necessary_condition_gradient
    {f : E → ℝ} {x₀ : E} {A : E →L[ℝ] E}
    (hmin : LocalMinimumAt f x₀)
    (hgrad : HasGradientAt f (0 : E) x₀)
    (hdiff_near : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ f x)
    (hHess : HasFDerivAt (fun x => gradient f x) A x₀) :
    PosSemidefOp A := by
  sorry

/-- 零算子是半正定的。 -/
theorem posSemidefOp_zero : PosSemidefOp (0 : E →L[ℝ] E) := by
  intro v
  simp

/-- 两个半正定算子的和仍是半正定的。 -/
theorem posSemidefOp_add {A B : E →L[ℝ] E}
    (hA : PosSemidefOp A) (hB : PosSemidefOp B) :
    PosSemidefOp (A + B) := by
  intro v
  dsimp [PosSemidefOp] at hA hB ⊢
  have h1 := hA v
  have h2 := hB v
  calc
    0 ≤ inner ℝ (A v) v + inner ℝ (B v) v := add_nonneg h1 h2
    _ = inner ℝ (A v + B v) v := by rw [inner_add_left]
    _ = inner ℝ ((A + B) v) v := by rw [add_apply]

/-- 半正定算子乘以非负标量仍是半正定的。 -/
theorem posSemidefOp_smul {A : E →L[ℝ] E} {c : ℝ}
    (hc : 0 ≤ c) (hA : PosSemidefOp A) :
    PosSemidefOp (c • A) := by
  intro v
  dsimp [PosSemidefOp] at hA ⊢
  have h := hA v
  calc
    0 ≤ c * inner ℝ (A v) v := mul_nonneg hc h
    _ = (starRingEnd ℝ c) * inner ℝ (A v) v := by simp
    _ = inner ℝ (c • (A v)) v := by rw [inner_smul_left]
    _ = inner ℝ ((c • A) v) v := by rw [ContinuousLinearMap.smul_apply]

/-- 常函数的 Hessian 处处为零。 -/
theorem hessianOp_const (c : ℝ) (x : E) : HessianOp (fun _ : E => c) x = 0 := by
  unfold HessianOp
  simp

section MatrixRepresentation

/-- `n` 维欧氏空间的简写。 -/
abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- 连续线性算子 `A` 在标准基下的矩阵表示，分量 `(i, j)` 为 `⟨eᵢ, A eⱼ⟩`。 -/
noncomputable def HessianMatrix {n : ℕ} (A : Euc n →L[ℝ] Euc n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => inner ℝ (EuclideanSpace.single i 1) (A (EuclideanSpace.single j 1))

end MatrixRepresentation
