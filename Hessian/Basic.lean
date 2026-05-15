import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped Topology
open ContinuousLinearMap
open SignType

set_option linter.unusedSectionVars false

namespace HessianPrototype

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `x₀` 是 `f` 的局部极小点。 -/
def localMinimumAt (f : E → ℝ) (x₀ : E) : Prop :=
  ∃ ε > 0, ∀ y : E, dist y x₀ < ε → f x₀ ≤ f y

/-- Hessian 算子：梯度场的 Fréchet 导数。 -/
noncomputable def hessianOp (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (fun y => gradient f y) x

/-- 连续线性算子半正定：对所有 `v` 都有 `⟪A v, v⟫ ≥ 0`。 -/
def posSemidefOp (A : E →L[ℝ] E) : Prop :=
  ∀ v : E, 0 ≤ inner ℝ (A v) v

/-- `f` 在 `x` 处的 Hessian 半正定。 -/
def hessianPosSemidefAt (f : E → ℝ) (x : E) : Prop :=
  posSemidefOp (hessianOp f x)

/-- 零算子半正定。 -/
theorem posSemidefOp_zero : posSemidefOp (0 : E →L[ℝ] E) := by
  intro v
  simp

/-- 两个半正定算子的和仍半正定。 -/
theorem posSemidefOp_add {A B : E →L[ℝ] E}
    (hA : posSemidefOp A) (hB : posSemidefOp B) :
    posSemidefOp (A + B) := by
  intro v
  dsimp [posSemidefOp] at hA hB ⊢
  have h1 := hA v
  have h2 := hB v
  calc
    0 ≤ inner ℝ (A v) v + inner ℝ (B v) v := add_nonneg h1 h2
    _ = inner ℝ (A v + B v) v := by rw [inner_add_left]
    _ = inner ℝ ((A + B) v) v := by rw [ContinuousLinearMap.add_apply]

/-- 半正定算子的非负标量倍仍半正定。 -/
theorem posSemidefOp_smul {A : E →L[ℝ] E} {c : ℝ}
    (hc : 0 ≤ c) (hA : posSemidefOp A) :
    posSemidefOp (c • A) := by
  intro v
  dsimp [posSemidefOp] at hA ⊢
  have h := hA v
  calc
    0 ≤ c * inner ℝ (A v) v := mul_nonneg hc h
    _ = (starRingEnd ℝ c) * inner ℝ (A v) v := by simp
    _ = inner ℝ (c • (A v)) v := by rw [inner_smul_left]
    _ = inner ℝ ((c • A) v) v := by rw [ContinuousLinearMap.smul_apply]

/-- 常函数的 Hessian 算子为零。 -/
theorem hessianOp_const (c : ℝ) (x : E) :
    hessianOp (fun _ : E => c) x = 0 := by
  unfold hessianOp
  simp

/-- 常函数的 Hessian 半正定。 -/
theorem hessianPosSemidefAt_const (c : ℝ) (x : E) :
    hessianPosSemidefAt (fun _ : E => c) x := by
  unfold hessianPosSemidefAt
  rw [hessianOp_const]
  exact posSemidefOp_zero

/-- 仿射直线 `t ↦ x₀ + t • v` 的导数是 `v`。 -/
lemma hasDerivAt_line (x₀ v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x₀ + s • v) v t := by
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id' (𝕜 := ℝ) (x := t)
  have hsmul : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa using HasDerivAt.smul_const hid v
  simpa using hsmul.const_add x₀

/-- 把局部极小点限制到任意仿射直线上，仍得到 `0` 处的一维局部极小。 -/
lemma localMinimumAt_comp_line {f : E → ℝ} {x₀ : E}
    (hmin : localMinimumAt f x₀) (v : E) :
    localMinimumAt (fun t : ℝ => f (x₀ + t • v)) 0 := by
  rcases hmin with ⟨ε, hε, hmin⟩
  refine ⟨ε / (‖v‖ + 1), ?_, ?_⟩
  · positivity
  · intro t ht
    have ht_abs : |t| < ε / (‖v‖ + 1) := by
      simpa [Real.dist_eq, abs_sub_comm] using ht
    have hden_pos : 0 < ‖v‖ + 1 := by positivity
    have hmul : |t| * (‖v‖ + 1) < ε := by
      rwa [lt_div_iff₀ hden_pos] at ht_abs
    have hnorm_le : ‖t‖ * ‖v‖ ≤ ‖t‖ * (‖v‖ + 1) := by
      gcongr
      linarith [norm_nonneg v]
    have hdist : dist (x₀ + t • v) x₀ < ε := by
      calc
        dist (x₀ + t • v) x₀ = ‖t • v‖ := by
          rw [dist_eq_norm]
          congr 1
          abel
        _ = ‖t‖ * ‖v‖ := norm_smul t v
        _ ≤ ‖t‖ * (‖v‖ + 1) := hnorm_le
        _ = |t| * (‖v‖ + 1) := by rw [Real.norm_eq_abs]
        _ < ε := hmul
    simpa using hmin (x₀ + t • v) hdist

/-- 若显式梯度场可用，则 `f` 沿直线限制的一维导数由内积给出。 -/
lemma hasDerivAt_comp_line_of_hasGradientAt
    {f : E → ℝ} {g : E → E} {x₀ v : E} {t : ℝ}
    (hgrad : HasGradientAt f (g (x₀ + t • v)) (x₀ + t • v)) :
    HasDerivAt (fun s : ℝ => f (x₀ + s • v))
      (inner ℝ (g (x₀ + t • v)) v) t := by
  have hcomp := hgrad.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line x₀ v t)
  simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hcomp

/-- 梯度场与方向向量的内积沿直线的一维导数。 -/
lemma hasDerivAt_inner_gradientField_line
    {g : E → E} {x₀ v : E} {A : E →L[ℝ] E}
    (hHess : HasFDerivAt g A x₀) :
    HasDerivAt (fun t : ℝ => inner ℝ (g (x₀ + t • v)) v)
      (inner ℝ (A v) v) 0 := by
  have hgline : HasDerivAt (fun t : ℝ => g (x₀ + t • v)) (A v) 0 := by
    have hHess' : HasFDerivAt g A (x₀ + (0 : ℝ) • v) := by simpa using hHess
    simpa [Function.comp_def] using hHess'.comp_hasDerivAt 0 (hasDerivAt_line x₀ v 0)
  have hv : HasDerivAt (fun _ : ℝ => v) (0 : E) 0 := hasDerivAt_const (x := 0) (c := v)
  have hinner := hgline.inner ℝ hv
  simpa using hinner

/-- 局部极小点的一维二阶必要条件。

这是当前证明中隔离出的实分析难点：需要证明如果 `φ` 在 `0` 处局部极小，
在 `0` 处导数为 `0`，并且局部导数字段 `φ'` 在 `0` 处导数为 `l`，则 `l ≥ 0`。
后续可用 LeanSearch / `#check` 搜索：`IsLocalMin`、`HasDerivAt.deriv`、
`deriv_nonneg_of_localMin`、斜率不等式，以及 `Filter.Tendsto` 的单侧商极限引理。 -/
lemma oneDim_secondOrderNecessary
    {φ φ' : ℝ → ℝ} {l : ℝ}
    (hmin : localMinimumAt φ 0)
    (hderiv : HasDerivAt φ 0 0)
    (hderiv' : HasDerivAt φ' l 0)
    (hφ' : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt φ (φ' t) t) :
    0 ≤ l := by
  by_contra hl_nonneg
  have hl_neg : l < 0 := lt_of_not_ge hl_nonneg
  have hφ'_zero : φ' 0 = 0 := by
    exact (hderiv.unique hφ'.self_of_nhds).symm
  have hderivφ'_eq : deriv φ' 0 = l := hderiv'.deriv
  have hsign : ∀ᶠ x in 𝓝 (0 : ℝ), sign (φ' x) = sign (0 - x) := by
    exact eventually_nhdsWithin_sign_eq_of_deriv_neg
      (f := φ') (x₀ := 0) (by simpa [hderivφ'_eq] using hl_neg) hφ'_zero
  have hneg_right : ∀ᶠ x in 𝓝[>] (0 : ℝ), φ' x < 0 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hsign, self_mem_nhdsWithin]
      with x hxsign hxpos
    have hxsign_neg : sign (φ' x) = -1 := by
      rw [hxsign]
      have hxpos' : 0 < x := hxpos
      exact sign_neg (by linarith)
    exact sign_eq_neg_one_iff.mp hxsign_neg
  have hderiv_right : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt φ (φ' x) x :=
    eventually_nhdsWithin_of_eventually_nhds hφ'
  rcases mem_nhdsGT_iff_exists_Ioo_subset.1 (hderiv_right.and hneg_right) with
    ⟨b₁, hb₁_pos, hb₁_subset⟩
  rcases hmin with ⟨ε, hε_pos, hminε⟩
  have hb₁_pos' : 0 < b₁ := hb₁_pos
  let b : ℝ := min b₁ ε / 2
  have hmin_pos : 0 < min b₁ ε := lt_min hb₁_pos' hε_pos
  have hb_pos : 0 < b := by positivity
  have hb_lt_b₁ : b < b₁ := by
    dsimp [b]
    have hmin_le : min b₁ ε ≤ b₁ := min_le_left b₁ ε
    nlinarith
  have hb_lt_ε : b < ε := by
    dsimp [b]
    have hmin_le : min b₁ ε ≤ ε := min_le_right b₁ ε
    nlinarith
  have hderiv_on : ∀ x ∈ Set.Ioo 0 b, HasDerivAt φ (φ' x) x := by
    intro x hx
    exact (hb₁_subset ⟨hx.1, hx.2.trans hb_lt_b₁⟩).1
  have hneg_on : ∀ x ∈ Set.Ioo 0 b, φ' x < 0 := by
    intro x hx
    exact (hb₁_subset ⟨hx.1, hx.2.trans hb_lt_b₁⟩).2
  have hcont : ContinuousOn φ (Set.Icc 0 b) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact hderiv.continuousAt.continuousWithinAt
    · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hx_lt_b₁ : x < b₁ := hx.2.trans_lt hb_lt_b₁
      exact ((hb₁_subset ⟨hx_pos, hx_lt_b₁⟩).1).continuousAt.continuousWithinAt
  rcases exists_hasDerivAt_eq_slope φ φ' hb_pos hcont hderiv_on with ⟨c, hc, hc_eq⟩
  have hc_neg : φ' c < 0 := hneg_on c hc
  have hslope_neg : (φ b - φ 0) / (b - 0) < 0 := by
    simpa [hc_eq] using hc_neg
  have hdiff_neg : φ b - φ 0 < 0 := by
    have hbden : 0 < b - 0 := by simpa using hb_pos
    have hmul_neg : ((φ b - φ 0) / (b - 0)) * (b - 0) < 0 :=
      mul_neg_of_neg_of_pos hslope_neg hbden
    rwa [div_mul_cancel₀ _ (ne_of_gt hbden)] at hmul_neg
  have hφb_lt : φ b < φ 0 := by linarith
  have hmin_b : φ 0 ≤ φ b := by
    apply hminε
    simpa [Real.dist_eq, abs_of_pos hb_pos] using hb_lt_ε
  linarith

/-- 使用显式梯度场表述的二阶必要条件。 -/
theorem second_order_necessary_condition_gradient_field
    {f : E → ℝ} {g : E → E} {x₀ : E} {A : E →L[ℝ] E}
    (hmin : localMinimumAt f x₀)
    (hgrad_near : ∀ᶠ x in 𝓝 x₀, HasGradientAt f (g x) x)
    (hgrad_zero : g x₀ = 0)
    (hHess : HasFDerivAt g A x₀) :
    posSemidefOp A := by
  intro v
  let φ : ℝ → ℝ := fun t => f (x₀ + t • v)
  let φ' : ℝ → ℝ := fun t => inner ℝ (g (x₀ + t • v)) v
  have hmin_line : localMinimumAt φ 0 := localMinimumAt_comp_line hmin v
  have hline_tendsto : Filter.Tendsto (fun t : ℝ => x₀ + t • v) (𝓝 (0 : ℝ)) (𝓝 x₀) := by
    simpa using (hasDerivAt_line x₀ v 0).continuousAt.tendsto
  have hgrad_line : ∀ᶠ t in 𝓝 (0 : ℝ), HasGradientAt f (g (x₀ + t • v)) (x₀ + t • v) :=
    hline_tendsto.eventually hgrad_near
  have hφ' : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt φ (φ' t) t := by
    filter_upwards [hgrad_line] with t ht
    exact hasDerivAt_comp_line_of_hasGradientAt (g := g) (x₀ := x₀) (v := v) ht
  have hgrad_at : HasGradientAt f (g x₀) x₀ := hgrad_near.self_of_nhds
  have hderivφ : HasDerivAt φ 0 0 := by
    have h := hasDerivAt_comp_line_of_hasGradientAt (g := g) (x₀ := x₀) (v := v) (t := 0) (by simpa using hgrad_at)
    simpa [φ, hgrad_zero] using h
  have hderivφ' : HasDerivAt φ' (inner ℝ (A v) v) 0 := by
    simpa [φ'] using hasDerivAt_inner_gradientField_line (g := g) (x₀ := x₀) (v := v) hHess
  exact oneDim_secondOrderNecessary hmin_line hderivφ hderivφ' hφ'

/-- 直接使用 mathlib 中非可计算 `gradient f` 字段的版本。 -/
theorem second_order_necessary_condition_gradient
    {f : E → ℝ} {x₀ : E} {A : E →L[ℝ] E}
    (hmin : localMinimumAt f x₀)
    (hgrad : HasGradientAt f (0 : E) x₀)
    (hdiff_near : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ f x)
    (hHess : HasFDerivAt (fun x => gradient f x) A x₀) :
    posSemidefOp A := by
  apply second_order_necessary_condition_gradient_field (g := fun x => gradient f x) hmin
  · exact hdiff_near.mono fun x hx => hx.hasGradientAt
  · exact hgrad.gradient
  · exact hHess

section MatrixRepresentation

/-- `n` 维欧氏空间。 -/
abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- 连续线性算子在标准基下的矩阵表示。 -/
noncomputable def hessianMatrixOfOp {n : ℕ} (A : Euc n →L[ℝ] Euc n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => inner ℝ (EuclideanSpace.single i 1) (A (EuclideanSpace.single j 1))

end MatrixRepresentation

end HessianPrototype
