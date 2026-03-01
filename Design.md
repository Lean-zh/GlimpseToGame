# Glimpse to Game — 设计文档

## 1. 项目概述

| 项目 | 说明 |
|------|------|
| **标题** | Glimpse to Game |
| **目标** | 将 [Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean) 教程完整转化为基于 **lean4game** 的关卡制游戏 |
| **受众** | 希望用交互式、分步闯关方式学习 Lean 4 的数学/逻辑初学者 |
| **参考** | 实现与校对时可对照 `GlimpseOfLean/GlimpseOfLean/Solutions/` 中的解答 |

**设计原则**

- **内容覆盖**：每个原始 `example`/`lemma` 都应对应到某一关的 `Statement`，不遗漏、不擅自删减。
- **风格统一**：遵循 lean4game 约定：每 World 一个总 `.lean` 文件 + 子目录下按关的 `Lxx_Name.lean`，每关使用 `Statement`、`Introduction`、`Hint`、`NewTactic`、`Conclusion` 等。
- **依赖一致**：关卡顺序与原始教程一致；先 Computing → Logic，再开放 Analysis / Set Theory / Algebra / Probability 等分支。

---

## 2. 源文件与 World 对应表

| 原始路径 (GlimpseOfLean) | 游戏 World | 说明 |
|---------------------------|------------|------|
| `Exercises/01Rewriting.lean` | **Rewriting** | 计算与改写：ring, rw, calc, exact |
| `Exercises/02Iff.lean` | **Logic**（前半） | 蕴涵、等价、↔ |
| `Exercises/03Forall.lean` | **Logic**（中段） | 全称 ∀、unfold、specialize、simp、apply? |
| `Exercises/04Exists.lean` | **Logic**（后半） | 合取 ∧、存在 ∃、rcases、use |
| `Exercises/Topics/SequenceLimits.lean` | **Analysis** | 数列极限、linarith、子列、聚点、Cauchy |
| `Exercises/Topics/GaloisAdjunctions.lean` | **SetTheory** | 偏序、inf/sup、完备格、Galois 连接 |
| `Exercises/Topics/RingTheory.lean` | **Algebra** | 环、同态、理想、商环、同构定理、中国剩余 |
| `Exercises/Topics/Probability.lean` | **Probability** | 独立性、条件概率、贝叶斯 |
| `Exercises/Topics/ClassicalPropositionalLogic.lean` | **PropositionalLogic**（可选） | 经典命题逻辑语法与语义 |
| `Exercises/Topics/IntuitionisticPropositionalLogic.lean` | **PropositionalLogic**（可选） | 直觉主义命题逻辑、Heyting 代数 |

说明：`Exercises/Shorter.lean` 为“短轨”，与 01–04 + Topics 有重叠，可不单独建 World，其题目可视为对主轨的补充或合并到对应 World。

---

## 3. World 与关卡设计（与原始题目一一对应）

### 3.1 World: Rewriting（Computing）

**源文件**：`GlimpseOfLean/Exercises/01Rewriting.lean`  
**Solutions**：`GlimpseOfLean/Solutions/01Rewriting.lean`

| Level | 标题建议 | 对应原始内容 | 要点 |
|-------|----------|--------------|------|
| 1 | The ring tactic (结合律) | `(a * b) * c = b * (a * c)` | `ring` |
| 2 | Expansion | `(a+b)^2 = a^2 + 2*a*b + b^2` | `ring` |
| 3 | Basic rewriting | `a + e = d + c` 用 `h : a = b+c`, `h' : b = d-e` 分步 `rw [h]` `rw [h']` | `rw`、`ring` |
| 4 | Multiple rewrites | 同上，一次 `rw [h, h']` | `rw` 多步 |
| 5 | Rewriting with assumptions | `a + b = c + 4*d` 用 `h : b = d+d`, `h' : a = b+c` | `rw` + `ring` |
| 6 | Rewriting with lemmas | `exp (a+b+c) = exp a * exp b * exp c`（exp_add） | `rw [exp_add]`、可带参数 |
| 7 | exp_sub / exp_zero | `exp (a+b-c) = (exp a * exp b)/(exp c * exp 0)` | `exp_sub`、`exp_zero`、`ring`/`mul_one` |
| 8 | Reverse rewriting | `b + c + e = d + c` 用 `h : a = b+c` 从右到左 `rw [← h]` | `rw [← h]` |
| 9 | Reverse rewriting exercise | `b + c = d` 用 `h : a = b+b`, `h' : b = c`, `h'' : a = d` | `rw [← …]` |
| 10 | Rewriting in an assumption | `c = d*a + d` 用 `rw [h'] at h` 再 `exact h` | `rw [...] at h`、`exact` |
| 11 | Calculation layout (calc) | `c = 0` 用 `h : c = b*a - d`, `h' : d = a*b` 的 calc | `calc`、`rw`、`ring` |
| 12 | calc with exp | `exp (2*a) = (exp b)^2 * (exp c)^2`（填空式 calc） | `calc`、`exp_add` |
| 13 | calc exercise | `c = 2*a*d` 用 `h : c = d*a + b`, `h' : b = a*d` | `calc`、`ring` |

**NewTactic 建议**：按关依次引入 `ring`、`rw`、`exact`、`calc`；需要时在 Introduction 中说明 `←` 与 `at h`。

---

### 3.2 World: Logic

**源文件**：`02Iff.lean` → `03Forall.lean` → `04Exists.lean`（严格按此顺序）

#### 3.2.1 来自 02Iff：蕴涵与等价

| Level | 标题建议 | 对应原始内容 | 要点 |
|-------|----------|--------------|------|
| L01 | Using implications | `0 < a^2` 用 `sq_pos_of_pos ha` | `exact` |
| L02 | Backward reasoning (apply) | `0 < (a^2)^2` 两次 `apply sq_pos_of_pos` 再 `exact ha` | `apply`、多目标 |
| L03 | add_pos (两个正数之和为正) | `0 < a^2 + b^2` 用 `add_pos`、`sq_pos_of_pos` | `apply`、分目标 |
| L04 | Forward reasoning (have) | `0 < (a^2)^2` 用 `have h2 : 0 < a^2 := …` 再 `exact sq_pos_of_pos h2` | `have` |
| L05 | have exercise | 同 L03 用 `have` 证明 `0 < a^2 + b^2` | `have` |
| L06 | Proving implications (intro) | `a > 0 → b > 0 → a + b > 0` 用 `intro ha hb`、`exact add_pos` | `intro` |
| L07 | Propositional logic | `(p → q) → (p → q → r) → p → r` | `intro`、`exact` |
| L08 | Equivalences (rw with ↔) | `c + a ≤ c + b ↔ a ≤ b` 用 `sub_nonneg`、`ring`、`rw` | `rw` + ↔ |
| L09 | add_le_add_iff_right | `a + c ≤ b + c ↔ a ≤ b` | 同上，可对照 `add_le_add_iff_right` |
| L10 | Using .2 of equivalence | `b ≤ a + b` 用 `(add_le_add_iff_right b).2 ha` | `h.1` / `h.2` |
| L11 | add_le_add_iff_left | `a ≤ a + b` 用 `add_le_add_iff_left` | ↔ 的方向 |
| L12 | Proving equivalences (constructor) | `(a-b)*(a+b) = 0 ↔ a^2 = b^2` 用 `constructor`、两向 calc | `constructor`、`·` |
| L13 | a = b ↔ b - a = 0 | `a = b ↔ b - a = 0` | 证明 ↔ |

#### 3.2.2 来自 03Forall：全称量词

| Level | 标题建议 | 对应原始内容 | 要点 |
|-------|----------|--------------|------|
| L14 | even_fun, unfold | `even_fun (f + g)` 用 `unfold`、`intro`、`calc`、`rw [hf x]` 等 | `unfold`、`intro`、`rfl` |
| L15 | Compressed ∀ proof | 同上，用 `intro hf hg x` 和 `rw [hf, hg]` | 简化写法 |
| L16 | even_fun (g ∘ f) | `even_fun (g ∘ f)` | ∀ 与函数复合 |
| L17 | non_decreasing, forward | `non_decreasing (g ∘ f)` 用 `have step₁` 再 `exact hg …` | `have`、`exact` |
| L18 | specialize | 同上，用 `specialize hf x₁ x₂ h` 再 `exact hg …` | `specialize` |
| L19 | Backward with apply | 同上，用 `apply hg`、`apply hf`、`exact h` | `apply` 与推断 |
| L20 | non_increasing (g ∘ f) | `non_increasing (g ∘ f)` 当 f 单调增、g 单调减 | 组合 |
| L21 | simp (Set) | `x ∈ (X ∩ Y) ∪ (X \ Y)` | `simp` |
| L22 | apply? | 紧支撑连续函数有全局最小值 `∃ x, ∀ y, f x ≤ f y` | `apply?` |

#### 3.2.3 来自 04Exists：合取与存在

| Level | 标题建议 | 对应原始内容 | 要点 |
|-------|----------|--------------|------|
| L23 | Conjunction (rcases, constructor) | `p ∧ q → r ∧ s` 用 `rcases`、`constructor` | `rcases`、`constructor` |
| L24 | Conjunction (⟨ , ⟩) | 同上，用 `⟨h hpq.1, h' hpq.2⟩` | 项式证明 |
| L25 | (p → (q → r)) ↔ p ∧ q → r | 命题逻辑等价，可选 `tauto` | `constructor` 或 `tauto` |
| L26 | Existential (use) | `∃ n : ℕ, 8 = 2*n` 用 `use 4` | `use` |
| L27 | Using ∃ (rcases) | `n > 0` 用 `h : ∃ k, n = k+1`、`rcases`、`rw`、`exact Nat.succ_pos` | `rcases` |
| L28 | Divisibility (a ∣ b) | `a ∣ b`、`b ∣ c` → `a ∣ c`（`use` + calc） | `a ∣ b`、`use` |
| L29 | Surjective | `Surjective (g ∘ f)` → `Surjective g` | `Surjective`、`use`、`rcases` |

**Logic World 实现注意**：当前已有 L01–L07（Implications, Forward, ProvingImplications, Equivalences, Forall, Exists, Conjunction），需对照上表补全 L08–L13（等价多关）与 L14–L22（∀、simp、apply?），并确保 L23–L29 与 04Exists 一致。Solutions 见 `Solutions/02Iff.lean`、`03Forall.lean`、`04Exists.lean`。

---

### 3.3 World: Analysis（Sequence Limits）

**源文件**：`GlimpseOfLean/Exercises/Topics/SequenceLimits.lean`  
**Solutions**：`GlimpseOfLean/Solutions/Topics/SequenceLimits.lean`

| Level | 标题建议 | 对应原始内容 | 要点 |
|-------|----------|--------------|------|
| 1 | linarith | `0 ≤ a + b`、`a + c ≤ b + d` 等 | `linarith` |
| 2 | seq_limit definition | 引入 `seq_limit`，常数列 `∀ n, u n = l` → `seq_limit u l` | `intro ε ε_pos`、`use 0`、`simp` |
| 3 | Positive limit lower bound | `l > 0` 时 ∃ N, ∀ n≥N, u n ≥ l/2 | `rcases`、`use`、`linarith`、`abs_*` |
| 4 | Limit of sum (triangle ineq) | `seq_limit (u+v) (l+l')` 用 ε/2、max N₁ N₂、`ge_max_iff`、`abs_add_le`、`linarith` | `rcases`、`use max`、`calc` |
| 5 | Squeeze theorem | `u ≤ v ≤ w` 且 u,w → l 则 v → l | `specialize`、`linarith`、`abs_le` |
| 6 | Uniqueness of limit | `seq_limit u l` 且 `seq_limit u l'` → `l = l'` | `eq_of_abs_sub_le_all` |
| 7 | non_decreasing, is_seq_sup | `is_seq_sup M u` + `non_decreasing u` → `seq_limit u M` | 定义展开、`use`、不等式 |
| 8 | extraction, id_le_extraction' | `extraction φ` → ∀ n, n ≤ φ n（归纳，可提供） | `extraction` 定义 |
| 9 | extraction_ge | `extraction φ` → ∀ N N', ∃ n ≥ N', φ n ≥ N | `∃ n ≥ N', _`、归纳或构造 |
| 10 | cluster_point, near_cluster | 聚点定义与“任意 ε,N 存在 n≥N 使 \|u n - a\| ≤ ε” | `rcases`、`use` |
| 11 | Subsequence tends to limit | `seq_limit u l`、`extraction φ` → `seq_limit (u ∘ φ) l` | `intro`、`use`、与 φ 单调性 |
| 12 | cluster_limit | `seq_limit u l`、`cluster_point u a` → `a = l` | `near_cluster`、`unique_limit` |
| 13 | Cauchy from convergent | `(∃ l, seq_limit u l)` → `CauchySequence u` | `rcases`、ε/2、max、`linarith` |
| 14 | Limit from Cauchy + cluster | `CauchySequence u`、`cluster_point u l` → `seq_limit u l` | `near_cluster`、Cauchy 定义 |

当前 GlimpseToGame 已有 L01–L04（SequenceLimit, SumLimit, SqueezeTheorem, Uniqueness），需与上表对齐并补全 L05–L14（若合并 linarith 为 L00 则编号顺延）。每关的 `Statement` 应与 Solutions 中对应 `example`/`lemma` 一致以保证可编译。

---

### 3.4 World: SetTheory（Galois Connections）

**源文件**：`GlimpseOfLean/Exercises/Topics/GaloisAdjunctions.lean`  
**Solutions**：`GlimpseOfLean/Solutions/Topics/GaloisAdjunctions.lean`

| Level | 标题建议 | 对应原始内容 | 要点 |
|-------|----------|--------------|------|
| 1 | lowerBounds / isInf | `isInf s x₀` 的定义与 `isInf.lowerBound` | `lowerBounds`、`isInf` |
| 2 | isInf.eq (唯一性) | `isInf s x₀`、`isInf s x₁` → `x₀ = x₁` | `le_antisymm`、`isInf` |
| 3 | isSup | `isSup` 定义、`isSup.upperBound`、`isSup.eq`（可引用对偶） | `upperBounds`、OrderDual |
| 4 | isInfFun / isSupFun | `isInfFun I`、`isSupFun S` 定义 | 函数版 inf/sup |
| 5 | isSup_of_isInf / isInf_of_isSup | 由 Inf 函构造 Sup、由 Sup 函构造 Inf | 对偶构造 |
| 6 | CompleteLattice.mk_of_Inf/Sup | 从 Inf/Sup 函数得到完备格 | `CompleteLattice` |
| 7 | Inf_pair / Sup_pair | `x ≤ x' ↔ Inf {x,x'} = x` 等 | 二元 inf/sup |
| 8 | isInfInter / isSupUnion | 集合的 ⋂₀、⋃₀ 为 inf/sup | Set 族 |
| 9 | adjunction 定义 | `adjunction l r` 与基本性质 | `adjunction` |
| 10 | image_preimage_adjunction | 映射的像-原像 Galois 连接 | 具体例子 |
| 11 | mk_right / mk_left | 由 l 构造 r、由 r 构造 l | Galois 构造 |
| 12+ | Topology（可选） | `isOpen_empty`、`isOpen_univ`、`SupTop` 等 | 若时间允许 |

当前仅有 SetTheory/L01_InfSup，需按上表扩展至至少 L02–L11，并与 Solutions 一致。

---

### 3.5 World: Algebra（Commutative Rings）

**源文件**：`GlimpseOfLean/Exercises/Topics/RingTheory.lean`  
**Solutions**：需从仓库或本地 Solutions 目录核对

| Level | 标题建议 | 对应原始内容 | 要点 |
|-------|----------|--------------|------|
| 1 | ring in CommRing | `x*(y+z) + y*(z+x) + z*(x+y) = …` | `ring`、`CommRing` |
| 2 | Ring homomorphism (simp) | `f (1 + x*y) + f 0 = 1 + f x * f y` | `simp`、环同态 |
| 3 | RingHom.comp | 定义 `comp` 并证明 map_one'/mul'/zero'/add' | `intro`、`simp` |
| 4 | RingEquiv.comp | 同构的复合 | 同构、symm |
| 5 | Ideal (加法与乘法闭) | `y*x + x*y - 0 ∈ I` 等 | `Ideal`、`I.add_mem` 等 |
| 6 | ker 与 x ∈ ker f ↔ f x = 0 | `x ∈ ker f ↔ f x = 0` | `Ideal.ker` |
| 7 | Ideal.inter | 定义并证明两个理想的交仍是理想 | `Ideal` 构造 |
| 8 | Quotient 运算 | 商环中乘法等（如 `x*y*z`） | `Ideal.Quotient` |
| 9 | Quotient 与等价 | `x - y ∈ I` → 商中相等 | `Quotient.eq` |
| 10 | ker (Quotient.mk I) = I | 商映射的核 | `Ideal.ker`、`Quotient` |
| 11 | kerLift | 从 R →+* S 得到 R/ker f →+* S | 同态分解 |
| 12 | First Isomorphism Theorem | `firstIsomorphismTheorem`（满射时 R/ker f ≃+* S） | 同构定理 |
| 13 | chineseMap, injective/surjective | 中国剩余定理的映射与单/满性 | `chineseMap`、`Fintype`、理想互素 |

当前仅有 Algebra/L01_RingHom，需按上表补全 L02–L13，并确保依赖 `GlimpseOfLean.Library.Ring`（或游戏内等价 Library）。

---

### 3.6 World: Probability

**源文件**：`GlimpseOfLean/Exercises/Topics/Probability.lean`  
**Solutions**：`GlimpseOfLean/Solutions/Topics/Probability.lean`

| Level | 标题建议 | 对应原始内容 | 要点 |
|-------|----------|--------------|------|
| 1 | IndepSet.symm | `IndepSet A B` → `IndepSet B A` | 独立性对称 |
| 2 | IndepSet.compl_right | `IndepSet A B` → `IndepSet A Bᶜ`（可测） | `compl_eq_univ_diff`、`measure_diff` 等 |
| 3 | IndepSet.compl_right_iff | `IndepSet A Bᶜ ↔ IndepSet A B` | iff、measurability |
| 4 | IndepSet.compl_left | `IndepSet Aᶜ B` 由 `IndepSet A B` 推出 | 用 compl_right |
| 5 | indep_self | `IndepSet A A` → ℙ A = 0 ∨ ℙ A = 1 | 讨论 ℙ A |
| 6 | condProb 定义与 zero_left/zero_right | ℙ(A\|B)、分子/分母为 0 的引理 | `condProb`、ENNReal |
| 7 | condProb_of_indepSet | 独立时 ℙ(A\|B) = ℙ A | 条件概率与独立性 |
| 8 | Bayes（若原文件有） | 贝叶斯公式 | 条件概率等式 |

当前已有 Probability/L01_Independence，需与上表对齐并补全 L02–L08；注意 `MeasureSpace`、`IsProbabilityMeasure`、`measurability` 等前置条件。

---

### 3.7 World: PropositionalLogic（可选）

**源文件**：`ClassicalPropositionalLogic.lean`、`IntuitionisticPropositionalLogic.lean`

- **经典**：Formula、IsTrue、Satisfies、Models、Valid；`Valid (~~A ⇔ A)` 等；Provable、weakening、deduction_theorem、Provable.mp；`Provable (A || ~A)` 等。
- **直觉主义**：eval（Heyting 代数）、Models、Valid；`Valid (~(A && ~A))`；Provable、De Morgan 等。

可单独做一个 World（如 5–8 关）或作为 Logic 的进阶分支，与 02/03/04 无强依赖，但需要命题逻辑符号（∧∨→↔¬）已在前面引入。

---

## 4. 依赖与解锁关系

- **入口**：Rewriting（Computing）为第一个 World。
- **Rewriting 通关后**：解锁 **Logic**。
- **Logic 通关后**：同时解锁 **Analysis**、**SetTheory**、**Algebra**、**Probability**（四者平行，无先后）。
- **PropositionalLogic**（若实现）：建议在 Logic 通关后解锁，或与 SetTheory/Algebra 并列。

与当前 `Game.lean` 中的 `Dependency Rewriting → Logic` 及 `Dependency Logic → Analysis/SetTheory/Algebra/Probability` 一致。

---

## 5. lean4game 实现规范

- **文件结构**
  - 每个 World 一个“总文件”，如 `Game/Levels/Rewriting.lean`、`Game/Levels/Logic.lean`，其中只做 `import Game.Levels.Rewriting.Lxx_*` 和 `World "Rewriting"`、`Title`、`Introduction`。
  - 每关一个文件，如 `Game/Levels/Rewriting/L01_Associativity.lean`，内含 `World "Rewriting"`、`Level n`、`Title`、`Introduction`、`Statement`、可选 `Hint`、`NewTactic`、`NewDefinition`、`Conclusion`。
- **Statement**
  - 与 GlimpseOfLean 中对应 `example`/`lemma` 的命题和类型一致；仅将 `example` 改为 `Statement ... := by ...`，证明可从 Solutions 移植后微调（如把注释变成 `Hint`）。
- **Hint**
  - 将原始教程中的“提示句”改为关卡内的 `Hint "..."`，便于玩家在卡住时逐步查看。
- **NewTactic / NewDefinition**
  - 在该 tactic/定义首次出现的关卡中声明，避免提前暴露后续内容。
- **编译**
  - 每关必须能通过 `lake build`（或项目使用的构建命令）；新增或修改关卡后应全量编译并跑测试（若有）。

---

## 6. 校对与开发清单

- [ ] **Rewriting**：13 关与 `01Rewriting.lean` 的 13 个 example 一一对应，且含“在假设中改写”与“exact”关。
- [ ] **Logic**：02Iff（L01–L13）、03Forall（L14–L22）、04Exists（L23–L29）全部覆盖；顺序与源文件一致；Solutions 已对照。
- [ ] **Analysis**：SequenceLimits 中 linarith、seq_limit、和极限、夹逼、唯一性、单调+上确界、子列、聚点、Cauchy 等全部成关；与 Solutions 一致且可编译。
- [ ] **SetTheory**：GaloisAdjunctions 从 isInf/isSup 到 adjunction、mk_left/mk_right 均有对应关卡。
- [ ] **Algebra**：RingTheory 从 ring、RingHom、Ideal、商、同构定理到中国剩余定理均有对应关卡；依赖 Library 正确。
- [ ] **Probability**：IndepSet、条件概率、贝叶斯等与 Probability.lean 一致；可测性等前提在 Introduction 或 Hint 中说明。
- [ ] **Game.lean**：Title、Introduction、Dependency 与本文档一致；所有 World 的 Level 编号连续且无遗漏导入。
- [ ] **全局**：无未使用的 import；所有 `Statement` 可证明且与原始题目等价；Hint 与原始教程表述对齐。

实现时优先保证“内容覆盖 + 编译通过”，再优化每关的 Introduction/Conclusion 文案和 Hint 的粒度。
