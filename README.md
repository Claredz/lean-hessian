# lean-hessian

这是一个围绕 Hessian 与二阶必要条件的 Lean 4 形式化尝试项目。

GitHub: <https://github.com/Claredz/lean-hessian>

## 项目定位

本项目来自课程小组项目背景，是我在 AI 工具辅助下进行的 Lean 4 / Mathlib 形式化尝试。项目目标是把多元微积分中“局部极小点处 Hessian 半正定”这一类二阶必要条件，用 Lean 4 中的 Fréchet derivative、gradient、inner product space 和 continuous linear map 等概念表达出来。

需要特别说明：本项目的 Lean 代码主要由 AI 辅助生成，我本人的参与更多在选题、理解目标命题、运行检查、整理说明和反思过程中。因此它不应被表述为我独立完成的形式化研究成果。这个项目让我意识到，“Lean 代码能够通过编译”并不等于自己真正理解了全部证明细节，也促使我希望系统学习 Lean、Mathlib 和形式化智能体辅助数学的方法。

## 主要内容

核心文件：

- `Hessian.lean`：项目根模块；
- `Hessian/Basic.lean`：主要形式化内容。

`Hessian/Basic.lean` 中目前包含：

- 局部极小点 `localMinimumAt` 的定义；
- Hessian operator `hessianOp`，即梯度映射的 Fréchet 导数；
- 连续线性算子的半正定性 `posSemidefOp`；
- Hessian 半正定性的封装；
- 半正定算子的基本闭包性质，例如零算子、加法、非负数乘；
- 常函数 Hessian 半正定的简单例子；
- 沿直线限制函数的一些导数引理；
- 梯度场版本的二阶必要条件；
- 使用 `gradient f` 表述的二阶必要条件；
- 欧氏空间中连续线性算子的矩阵表示。

## 当前状态

- Lean 版本：`leanprover/lean4:v4.29.1`
- mathlib 版本：`v4.29.1`
- 本地检查：使用对应 Lean 版本运行 `lake build` 可以通过。
- 尚无专门测试套件。

## 构建方式

在项目根目录运行：

```powershell
lake build
```

或者显式指定 Lean 版本：

```powershell
elan run leanprover/lean4:v4.29.1 lake build
```

也可以单独检查主文件：

```powershell
lake env lean Hessian/Basic.lean
```

## 局限与反思

这个项目更适合作为一次 AI 辅助形式化的探索，而不是成熟的数学形式化成果。后续如果继续推进，我需要重点补足：

- 对 Mathlib 微积分接口的系统理解；
- 对 `HasFDerivAt`、`HasGradientAt`、`gradient` 等对象之间关系的掌握；
- 对每个关键证明步骤的人工复核；
- 将 AI 生成代码转化为自己真正理解、可解释、可维护的证明。
