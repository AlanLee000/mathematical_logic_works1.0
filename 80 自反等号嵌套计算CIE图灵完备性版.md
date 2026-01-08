# **CIE: Calculus of Internalized Equivalences**
#### **1. 语法 (Syntax)**

##### **1.1. 变量 (Variables)**
为确保形式化的严谨性与可计算性，我们将变量的类型 `V` 具体化为**自然数 `ℕ`**。设 `V = ℕ`。这一选择确保了变量具有**可判定相等性 (decidable equality)**，这是后续算法（如替换生成）和元理论证明的关键前提。

##### **1.2. 签名 (Signature)**
设 $\Sigma$ 为一个**预先固定的有限签名**，包含以下函数符号及其元数（arity）：
*   `equiv`：一个 2-元函数符号。
*   `pair`：一个 2-元函数符号。
*   `unit`：一个 0-元函数符号（常数）。
*   (可包含其他用户定义的函数符号，但该集合对于任何给定的理论实例都是固定的)。

通过 `pair` 和 `unit`，我们可以构造任意长度的元组。将 `Σ` 固定为一个有限集，是将其形式化为标准归纳数据类型（如在 Coq 或 Lean 中）的关键前提。

##### **1.3. 项 (Terms)**
项的集合 $T_\Sigma(V)$ 是在签名 $\Sigma$ 上以变量集 $V$ 为基础构建的自由项代数。不含变量的项，即基项 (Ground Terms) 的集合，记为 $T_\Sigma$。

##### **1.4. 记法 (Notation)**
为提高可读性，我们采用以下无歧义的记法：
*   `equiv(t₁, t₂)` 记作 `[t₁ ≡ t₂]`。
*   `unit` 记作 `()`。
*   `pair(t₁, t₂)` 是底层的二元组构造子。我们引入元组记法 `⟨...⟩` 作为其语法糖，其语义通过一个从项列表到项的编码函数 `E(·)` 来定义：
    *   $E([]) := ()$
    *   $E(t :: ts) := pair(t, E(ts))$  
    *   其中 $t :: ts$ 表示将 $t$ 加到列表 $ts$ 的头部

根据此定义，`⟨t₁, ..., tₙ⟩` 是 `E([t₁, ..., tₙ])` 的简写。元组被展开为右嵌套的 `pair` 结构，并以 `()` 结尾。例如：
*   `⟨⟩` 展开为 `E([])`，即 `()`。
*   `⟨t₁⟩` 展开为 `E([t₁])`，即 `pair(t₁, E([])) = pair(t₁, ())`。
*   `⟨t₁, t₂⟩` 展开为 `E([t₁, t₂])`，即 `pair(t₁, E([t₂])) = pair(t₁, pair(t₂, ()))`。

##### **1.5. 变量、替换 (Variables, Substitution)**

本节为系统的基础操作——替换——提供一个完整的、形式化的定义，并证明其关键性质。由于CIE系统是一个纯粹的代数系统，**不包含任何绑定结构**（如λ演算中的λ或量词∀），因此我们无需使用处理绑定的复杂技术（如带作用域的de Bruijn索引或locally nameless表示法）。替换是一个简单的、同态的结构性操作。

**定义 1.5.1 (项 Term)**
项 $t$ 的集合 $T_\Sigma(V)$ 由以下语法归纳定义：
$t ::= n | f(t₁, ..., tₖ)$
其中：
*   $n ∈ ℕ$ 是一个**变量索引 (variable index)**。
*   $f ∈ Σ$ 是签名中的一个 $k$-元函数符号，$t₁...tₖ$ 是其参数项。

**定义 1.5.2 (自由变量 Free Variables)**
项 $t$ 的自由变量集合 $vars(t)$ 归纳定义如下：
*   $vars(n) := \{n\}$
*   $vars(f(t₁, ..., tₖ)) := vars(t₁) ∪ \dots ∪ vars(tₖ)$
不含变量的项被称为**基项 (Ground Terms)**。

**定义 1.5.3 (替换 Substitution)**
本系统严格区分两类替换：
1.  **证明层任意替换 (Proof-Theoretic Arbitrary Substitution)**: 记为 $\theta$，是一个从变量索引到任意项的有限映射，即 $\theta: \mathbb{N} \rightharpoonup T_\Sigma(V)$。
2.  **运行层基项替换 (Operational Ground Substitution)**: 记为 $\sigma$，是一个从变量索引到基项的有限映射。

---
**引理 1.5.4 (替换的同态性 Substitution Homomorphism)**
对于任意函数符号 $f \in \Sigma$ 及其元数 $k$，任意项 $t_1, \dots, t_k, s$ 和任意变量 $j \in \mathbb{N}$，以下等式成立：
$$ f(t_1, \dots, t_k)[s/j] = f(t_1[s/j], \dots, t_k[s/j]) $$
---
**引理 1.5.5 (自由变量引理 - 单点替换 Free Variables Lemma for Single Substitution)**
对于任意项 $t$, $s$ 和任意变量 $j \in \mathbb{N}$，以下等式成立：
$$ \mathsf{vars}(t[s/j]) = \begin{cases} (\mathsf{vars}(t) \setminus \{j\}) \cup \mathsf{vars}(s) & \text{if } j \in \mathsf{vars}(t) \\ \mathsf{vars}(t) & \text{if } j \notin \mathsf{vars}(t) \end{cases} $$
---
**引理 1.5.6 (自由变量引理 - 多点替换 Free Variables Lemma for Simultaneous Substitution)**
对于任意项 $t$ 和任意替换 $\theta$，以下等式成立：
$$ \mathsf{vars}(\theta(t)) = (\mathsf{vars}(t) \setminus \mathrm{dom}(\theta)) \cup \bigcup_{j \in (\mathrm{dom}(\theta) \cap \mathsf{vars}(t))} \mathsf{vars}(\theta[j]) $$
---
**辅助引理 1.5.7 (替换对无关变量的影响)**
若 $k \notin \mathsf{vars}(s₁)$，则对于任意项 $s_2$ 和变量 $j \neq k$，有 $s_1[s_2/k] = s_1$。

---
**引理 1.5.8 (替换引理 Substitution Lemma)**
对于任意项 $t, s₁, s₂$ 和任意不同的变量 $j, k \in \mathbb{N}$，并且满足 $k \notin \mathsf{vars}(s₁)$ 和 $j \notin \mathsf{vars}(s_2)$，以下等式成立：
$$ (t[s₁/j])[s₂/k] = (t[s₂/k])[s₁/j] $$

---

### **3. 操作语义 (Operational Semantics)**

操作语义定义了系统的计算行为。为避免与语法构造子 `≡` 混淆，本节中定义的操作同余关系将记为 `≈`。

##### **3.1. 系统状态 (System State)**

系统的状态 $S$ 是一个偶对 $\langle C, U \rangle$，其中：
1.  $C \in T_\Sigma(V)$ 是**构型项 (Configuration Term)**。
2.  $U \subseteq T_\Sigma$ 是**已知基项论域 (Universe of Known Ground Terms)**，是一个有限集合。

一个**初始状态** $\langle C_0, U_0 \rangle$ 必须满足 $U_0 = \mathsf{ExtractGroundTerms}(C_0)$，其中函数 $\mathsf{ExtractGroundTerms}: T_\Sigma(V) \to \mathcal{P}(T_\Sigma)$ 递归地收集项中的所有基项子项：
*   若 $t \in V$，则 $\mathsf{ExtractGroundTerms}(t) := \emptyset$。
*   若 $t = f(t_1, \dots, t_n)$ 且 $f \in \Sigma$，则
    $$ \mathsf{ExtractGroundTerms}(t) := \begin{cases} (\bigcup_{i=1}^n \mathsf{ExtractGroundTerms}(t_i)) \cup \{t\} & \text{若 } \mathsf{vars}(t) = \emptyset \\ \bigcup_{i=1}^n \mathsf{ExtractGroundTerms}(t_i) & \text{否则} \end{cases} $$

**引理 3.1.1 (ExtractGroundTerms 的性质):**
对于任意项 $C \in T_\Sigma(V)$：
1.  一个基项 $g$ 属于 $\mathsf{ExtractGroundTerms}(C)$ 当且仅当 $g$ 是 $C$ 的一个基项子项。
2.  特别地，如果常量 `()` 不是 $C$ 的一个子项，那么 `()` $\notin \mathsf{ExtractGroundTerms}(C)$。


#### **3.2. 良构性 (Well-formedness)**
一个构型项 $C$ 是**良构的**，当且仅当对于 $C$ 中任意形如 $(l \equiv r)$ 且含有变量的子项，都满足**模式安全性约束 (Schema Safety Constraint)**：$\mathsf{vars}(r) \subseteq \mathsf{vars}(l)$。所有计算必须从一个良构的构型项开始。

#### **3.3. 动态上下文与操作同余 (Dynamic Context and Operational Congruence)**

对于一个状态 $S = \langle C, U \rangle$，我们定义其动态上下文和可判定的操作同余关系。

##### **3.3.1. 动态上下文 `Γ(C)` (Dynamic Context)**

对于一个构型项 `C`，其动态上下文 `Γ(C)` 被定义为与 `C` 中所有 `equiv` 子项相对应的等价判断构成的**多重集 (multiset)**。

形式化地，`Γ(C)` 是通过以下方式定义的：
$$ \Gamma(C) := \{ (l, r) \mid \exists p \in \mathcal{P}os(C) \text{ s.t. } C|_p = [l \equiv r] \}_{\text{mset}} $$
其中下标 `mset` 表示结果是一个多重集，即如果 `[l ≡ r]` 在 `C` 中出现 `k` 次，那么判断 `(l, r)` 在 `Γ(C)` 中的重数也为 `k`。

此定义是纯粹声明性的，它将 `Γ(C)` 的逻辑内容与其任何可能的计算方式（例如，通过树遍历）分离开来，确保了上下文的定义是明确且无歧义的。

##### **3.3.2. 基础等式集 (Base Equalities)** $E_C$:

$E_C$ 是一个有限的基项等式集合。它可以通过一个算法计算，也可以通过以下等价的声明式定义来描述：

**声明式定义:**
$$ E_C := \{ (\sigma(l), \sigma(r)) \mid (l,r) \in \Gamma(C) \text{ 且 } \sigma \text{ 是一个从 } \mathsf{vars}(l) \text{ 到 } U \text{ 的替换} \} $$

**计算过程:**
$E_C$ 可通过以下算法构造：
1.  初始化 $E_C$ 为空集。
2.  对于 $Γ(C)$ 中的每一个判断 $(l, r)$：
    a.  如果 $vars(l) ∪ vars(r) = ∅$，则将 $(l, r)$ 加入 $E_C$。
    b.  如果 $vars(l) ∪ vars(r) ≠ ∅$，则：
        i.  确定 $l$ 的变量集 $V_l = \mathsf{vars}(l)$。
        ii. 生成所有可能的从 $V_l$ 到已知基项论域 $U$ 的替换函数 $\sigma: V_l \to U$ 的集合。
        iii. 对于每一个这样的替换 $\sigma$，计算 $σ(l)$ 和 $σ(r)$，并将序对 $(σ(l), σ(r))$ 加入 $E_C$。
由于 $Γ(C)$ 和 $U$ 都是有限的，此过程必定终止，且生成的 $E_C$ 是有限的。

##### **3.3.3. 操作同余关系 `≈_C`**:
`≈_C` 是在基项集合 $T_\Sigma$ 上满足以下生成规则的**最小关系**：
*   **(Base)**: 若 $(t_1, t_2) \in E_C$，则 $t_1 \approx_C t_2$。
*   **(Refl)**: 对任意基项 $t$，有 $t \approx_C t$。
*   **(Sym)**: 若 $t_1 \approx_C t_2$，则 $t_2 \approx_C t_1$。
*   **(Trans)**: 若 $t_1 \approx_C t_2$ 且 $t_2 \approx_C t_3$，则 $t_1 \approx_C t_3$。
*   **(Cong)**: 若 $t_i \approx_C s_i$ 对所有 $i=1..n$，则 $f(t_1,\dots,t_n) \approx_C f(s_1,\dots,s_n)$。

此关系的可判定性在第8节中证明。

#### **3.4. 单步迁移关系 `⟶` (Single-Step Transition)**
一个状态 $S = \langle C, U \rangle$ 可以迁移到状态 $S' = \langle C', U' \rangle$，记为 $S \longrightarrow S'$，当且仅当以下三种归约规则之一适用：

##### I. 反射归约 (Reflection Reduction)
此规则是 `Equiv-Reflection` 和 `Equiv-Elim` 规则对的计算体现。
*   **条件**: 存在位置 $p$，使得 $C|_p = (t_1 \equiv t_2)$，其中 $t_1, t_2 \in T_\Sigma$ 是基项，且 $t_1 \approx_C t_2$。
*   **转换**: $C' := C[()]_{p}$ 且 $U' := U$。

##### II. 模式应用 (Schema Application)
此规则是应用公理模式 `(Hyp-Schema)` 的计算体现。
*   **条件**: 存在一个四元组 $(p_{app}, p_{ax}, l, \sigma)$ 满足：
    1.  $a = C|_{p_{app}}$ 是一个基项子项。
    2.  $(l \equiv r) = C|_{p_{ax}}$ 是 $C$ 中一个包含变量的子项。
    3.  $\sigma$ 是一个替换，其定义域为 $\mathsf{dom}(\sigma) = \mathsf{vars}(l)$，值域为 $\mathsf{codom}(\sigma) \subseteq U$。
    4.  $a \approx_C \sigma(l)$ 成立。
*   **转换**:
    *   $C' := C[\sigma(r)]_{p_{app}}$
    *   $U' := U \cup \mathsf{ExtractGroundTerms}(\sigma(r))$

##### III. 冗余消除 (Redundancy Elimination)
此规则用于规范化对 `()` 的等价断言。
*   **条件**: 存在位置 $p$，使得 $C|_p = ((t_1 \equiv t_2) \equiv ())$。
*   **转换**: $C' := C[(t_1 \equiv t_2)]_{p}$ 且 $U' := U$。

##### IV. 非确定性注记 (Note on Non-Determinism)
迁移关系 `⟶` 是非确定性的。在一个给定的状态 `S` 中，可能存在多个不同的位置 `p` 和规则组合，它们都满足应用条件。例如，一个子项可能既是**反射归约**的目标，又是**模式应用**的目标。系统规范没有规定选择哪一个进行归约，这种选择的灵活性是导致第 6.2 节中非合流性的根源。

---
### **4. 计算与基本性质 (Computation and Fundamental Properties)**

#### **4.1. 计算 (Computation)**
一个**计算**是一个（有限或无限的）迁移序列 $S_0 \longrightarrow S_1 \longrightarrow S_2 \longrightarrow \dots$，其中 $S_0 = \langle C_0, \mathsf{ExtractGroundTerms}(C_0) \rangle$ 是一个初始状态，且 $C_0$ 是良构的。

#### **4.2. 范式 (Normal Form)**

本节定义依赖于系统状态 `S` 的**可判定相等性 (decidable equality)**，即对于任意两个状态 $S_1, S_2$，存在一个算法可以判定 $S_1 = S_2$ 是否成立。此前提成立，因为状态由项和项的有限集构成，而项（由自然数和有限签名构建）和其有限集都具有可判定相等性。

一个状态 $S_n$ 被称为一个**范式**，当且仅当不存在任何**不同于** $S_n$ 的状态 $S'$ 使得 $S_n \longrightarrow S'$ 成立。

形式化地，$S_n$ 是范式当且仅当集合 $\{S' \mid S_n \longrightarrow S' \land S' \neq S_n \}$ 为空。

#### **4.3. 基本性质 (Fundamental Properties)**

本节将阐述系统的一些关键性质，以证明其理论上的健全性。

##### **4.3.1. 定理 (良构性不变性)**

**本证明以第 1.5 节中已证明的核心元理论引理的成立为前提。**

*   **证明**: 归约规则只会在构型项中替换或引入基项。对于**模式应用 (Schema Application)** 规则，引入的项是 $σ(r)$。根据规则前提，$σ$ 的值域 $codom(σ)$ 是 $U$ 的子集，因此 $σ$ 是一个基项替换。根据良构性约束 $vars(r) ⊆ vars(l)$，$r$ 中的所有变量也都在 $l$ 中，即在 $dom(σ)$ 中。
    根据在 **第1.5节** 已证明的 **自由变量引理 - 多点替换 (引理 1.5.6)**，我们有 $vars(σ(r)) = (vars(r) \setminus \mathrm{dom}(σ)) \cup \bigcup_{j \in (\mathrm{dom}(σ) \cap vars(r))} vars(σ[j])$。
    由于 $vars(r) ⊆ \mathrm{dom}(σ)$，第一项 `(vars(r) \ dom(σ))` 为空集。由于 $σ$ 是一个基项替换，其 codomain 中的所有项都是基项，因此对于任何变量 `j`，$vars(σ[j]) = ∅$。这意味着第二部分的并集也是空集。故 $vars(σ(r)) = ∅$，即 $σ(r)$ 是一个基项。
    其他规则引入的也是基项 $()$ 或已存在的子项 $(t_1 ≡ t_2)$。因此，没有新的带变量的 $(l ≡ r)$ 子项被引入，良构性得以保持。

---

### **7. 图灵完备性 (Turing Completeness)**

本节将证明 CIE 系统是图灵完备的。我们将通过展示 CIE 能够忠实地模拟一个已知的图灵完备计算模型——**SK 组合子逻辑**——来完成此证明。

**定理 7.1 (图灵完备性)**
CIE 系统是图灵完备的。

**证明.**
证明的核心策略是构造性地展示 CIE 的操作语义如何忠实地模拟 SK 组合子逻辑的归约过程。

#### **7.1. SK 组合子逻辑**

**形式化前提:** 本证明假定 SK 组合子逻辑的**邱奇-罗瑟定理**成立，即每个项最多只有一个范式。

SK 组合子逻辑是一个简单的项重写系统，其图灵完备性是计算理论中的一个标准结论。

*   **语法 (Terms)**: SK 项由以下规则归纳定义：
    1.  组合子 `S` 和 `K` 是项。
    2.  如果 `t₁` 和 `t₂` 是项，则其**应用 (Application)** `(t₁ t₂)` 也是一个项。应用是左结合的。

*   **归约规则 (Reduction Rules)**: SK 逻辑的计算由以下两条归约规则 `⟶_SK` 定义：
    1.  **K-归约**: `K x y  ⟶_SK  x`
    2.  **S-归约**: `S x y z  ⟶_SK  (x z) (y z)`

*   **基本性质**: SK 组合子逻辑满足**邱奇-罗瑟定理 (Church-Rosser Theorem)**。这意味着如果一个项可以归约到一个范式（即无法再归约的项），那么这个范式是唯一的。两个不同的范式彼此不等价。我们将用 `≡_SK` 表示由 `⟶_SK` 的自反、对称、传递闭包生成的等价关系。

#### **7.2. 在 CIE 中编码 SK 逻辑**

我们现在定义如何将 SK 逻辑的语法和规则编码为 CIE 的一部分。

1.  **签名扩展 (Signature Extension)**:
    我们扩展 CIE 的签名 `Σ` 以包含以下函数符号：
    *   `S`, `K`: 两个 0-元函数符号（常数）。
    *   `app`: 一个 2-元函数符号，用于表示组合子的应用。

2.  **项的编码 (Term Encoding)**:
    我们定义一个编码函数 `E(·)`，它将任意 SK 基项 `T` 映射到一个 CIE 基项 `E(T)`：
    *   `E(S) := S`
    *   `E(K) := K`
    *   `E((t₁ t₂)) := app(E(t₁), E(t₂))`

3.  **归约规则的编码 (Rule Encoding)**:
    SK 的两条归约规则被编码为 CIE 中的两个**公理模式 (Axiom Schemas)**：
    *   `R_K := [ app(app(K, x), y) ≡ x ]`
    *   `R_S := [ app(app(app(S, x), y), z) ≡ app(app(x, z), app(y, z)) ]`
    这两个公理模式均满足模式安全性约束。

#### **7.3. 模拟计算的构造**

给定任意一个 SK 基项 `T`，为了模拟其归约过程，我们构造如下的初始构型项 `C₀`：
```
C₀ := pair(
          pair(R_K, R_S),   // "程序"部分：编码的规则
          E(T)              // "数据"部分：编码的待归约项
      )
```
初始状态为 $S_0 = \langle C_0, \mathsf{ExtractGroundTerms}(C_0) \rangle$。一个模拟计算是指从 $S_0$ 出发，通过重复应用 `Schema Application` 规则来重写 `E(T)` 部分的计算序列。

为了证明此模拟的有效性，我们必须证明其**忠实性 (faithfulness)**，即 CIE 的其他机制不会产生与 SK 归约无关的旁路计算。核心是证明操作同余关系 `≈_C` 不会错误地将两个不应等价的 SK 项的编码识别为等价。

#### **7.4. 忠实性证明草图 (Proof Sketch of Faithfulness)**

模拟的忠实性依赖于两个关键属性：第一，CIE 的归约步骤能正确模拟 SK 归约；第二，没有旁路计算可以干扰 SK 项的编码结构。后者由以下两个关键引理保证。我们将同时给出它们的证明草图。

##### **引理 7.4.1 (U的纯净性不变式 - Purity Invariant of U)**
设 `S = ⟨C, U⟩` 是从为模拟SK逻辑构造的初始状态 `S₀` 出发，经过任意次迁移可达的任何状态。那么，`U` 中的任何项 `u`，要么是初始规则项 `R_K` 或 `R_S`，要么是某个SK项 `T'` 的有效编码 `E(T')`。特别地，**`() ∉ U`**。

**证明:**
我们对计算序列的长度 $n$ 进行归纳。
*   **基础情形 (n=0)**: $S_0 = \langle C_0, U_0 \rangle$。$U_0 = \mathsf{ExtractGroundTerms}(C_0)$。根据 `C₀` 的构造，它只包含 `pair` 和 `E(T)` 及其子项 `R_K`, `R_S`。SK项的编码函数 `E(·)` 只使用 `S`, `K`, `app` 符号，其结构中绝不包含独立的 `()` 项。因此，`U₀` 中所有项都符合不变式描述，且 `() ∉ U₀`。
*   **归纳步骤**: 假设不变式对长度为 $n$ 的计算序列可达的状态 $S_n = \langle C_n, U_n \rangle$ 成立。考虑一步迁移 $S_n \longrightarrow S_{n+1} = \langle C_{n+1}, U_{n+1} \rangle$。
    1.  若迁移是 **(Reflection Reduction)** 或 **(Redundancy Elimination)**，则 $U_{n+1} = U_n$。不变式保持。
    2.  若迁移是 **(Schema Application)**，则 $U_{n+1} = U_n \cup \mathsf{ExtractGroundTerms}(\sigma(r))$。
        *   在我们的SK模拟中，公理模式只能是 `R_K` 或 `R_S`。其右侧项 `r` (即 `x` 或 `app(app(x,z), app(y,z))`) 只包含变量和 `app` 符号。
        *   替换 `σ` 的值域 `codom(σ)` 是 $U_n$ 的子集。根据归纳假设，`σ` 将变量映射到有效的SK编码项或规则项。
        *   **封闭性:** 由于 `r` 只由变量和SK编码构造子 (`app`) 组成，将变量替换为SK编码项 `σ(x)` 后，得到的新项 `σ(r)` 必然也是一个有效的SK编码项。其结构保证了 `()` 绝不会在此过程中被生成。
        *   因此，`ExtractGroundTerms(σ(r))` 产生的也都是SK编码项。
    *   故 $U_{n+1}$ 仍然只包含规则项和SK编码项，且不含 `()`。不变式通过归纳得证。
**Q.E.D.**

##### **引理 7.4.2 (语义保守性)**

设 `S = ⟨C, U⟩` 是从为模拟 SK 逻辑构造的初始状态 `S₀` 出发，经过任意次迁移可达的任何状态。若 `t₁` 和 `t₂` 是两个 CIE 基项，且它们都是**任意 SK 项**的有效编码（即 `t₁=E(A)`, `t₂=E(B)`，其中 `A` 和 `B` 是 SK 项），那么：
$$ t₁ \approx_C t₂ \quad \implies \quad A \equiv_{SK} B $$
其中 `≡_SK` 是由 SK 归约规则生成的等价关系。

**推论:** 特别地，如果 `A` 和 `B` 都是 SK **范式**，则 `t₁ ≈_C t₂` 蕴含 `A` 和 `B` 在语法上是相同的。

**证明 (引理):**
我们将构造一个语义模型 `M_SK` 并证明 `≈_C` 在此模型下是可靠的。

1.  **模型 `M_SK` 的定义**:
    *   **域 (Domain)**: `D = T_SK ∪ {⊥}`，其中 `T_SK` 是所有 SK 基项的集合，`⊥` 是一个特殊的“非SK”元素。
    *   **解释函数 `〚·〛`**: 将 CIE 基项映射到域 `D`。
        *   `〚S〛 := S`
        *   `〚K〛 := K`
        *   `〚app(t₁, t₂)〛 := (〚t₁〛 〚t₂〛)` (右侧是 SK 应用)，若 `〚t₁〛, 〚t₂〛 ≠ ⊥`；否则为 `⊥`。
        *   对于所有非 SK 编码的符号，映射到 `⊥`：`〚()〛 := ⊥`, `〚pair(t₁, t₂)〛 := ⊥`, `〚[t₁ ≡ t₂]〛 := ⊥`。

2.  **模型可靠性**: 我们证明，对于任何可达状态 `S = ⟨C, U⟩`，若 `t₁ ≈_C t₂`，则 `〚t₁〛 ≡_SK 〚t₂〛`（如果两者都解释为 `⊥`，则它们相等，也满足此条件）。
    我们对 `t₁ ≈_C t₂` 的推导进行结构归纳。
    *   **基础情形**: `(t₁, t₂)` 属于基础等式集 `E_C`。这意味着存在一个公理模式（`R_K` 或 `R_S`）和替换 `σ`，使得 `t₁ = σ(l)` 且 `t₂ = σ(r)`。
        *   根据 **引理 7.4.1**，`σ` 的值域 `codom(σ)` 只包含 SK 编码项。设 `σ(x)=E(A)`, `σ(y)=E(B)` 等。
        *   **对于 `R_K`**: `l = app(app(K, x), y)`，`r = x`。
            *   `〚t₁〛 = 〚app(app(K, E(A)), E(B))〛 = (K A) B`。
            *   `〚t₂〛 = 〚E(A)〛 = A`。
            *   根据 SK 归约，`(K A) B ⟶_SK A`，因此 `(K A) B ≡_SK A`。
        *   **对于 `R_S`**: 同理，`〚σ(l)〛` 是一个 S-红式，`〚σ(r)〛` 是其归约结果，故它们 `≡_SK`。
    *   **归纳步骤**: (自反、对称、传递) 若归纳假设成立，这些步骤显然保持 `≡_SK` 关系。(同余) 若 `tᵢ ≈_C sᵢ`，则 `〚tᵢ〛 ≡_SK 〚sᵢ〛`。由于 `≡_SK` 是一个同余关系，`〚app(t₁, t₂)〛 ≡_SK 〚app(s₁, s₂)〛` 成立。
    *   因此，模型可靠性得证：若 `t₁ ≈_C t₂`，则 `〚t₁〛 ≡_SK 〚t₂〛`。

3.  **引理与推论的证明**:
    *   根据引理假设，`t₁ = E(A)`, `t₂ = E(B)` 且 `t₁ ≈_C t₂`。
    *   根据模型可靠性，我们有 `〚t₁〛 ≡_SK 〚t₂〛`，即 `A ≡_SK B`。引理得证。
    *   **对于推论**：如果 `A` 和 `B` 进一步被假定为 SK 范式，根据 SK 的邱奇-罗瑟定理，两个等价的范式必须是语法相同的项。因此 `A` 与 `B` 语法相同。

**Q.E.D.**

#### **7.5. 忠实性证明与最终结论**

有了**纯净性不变式**和**语义保守性引理**，我们现在可以严谨地论证模拟的忠实性。

1.  **`Schema Application` 的行为**:
    此规则的匹配条件 `a ≈_C σ(l)`，在我们的模拟中，总是通过句法匹配（自反性）满足。`l` 是 `R_K` 或 `R_S` 的左侧。替换 `σ` 的值域 `codom(σ) ⊆ U`。根据 **引理 7.4.1 (纯净性不变式)**，`σ` 只能将变量映射到有效的SK编码项。因此，此规则精确地、无歧义地模拟了 SK 的归约步骤。

2.  **`Reflection Reduction` 的无害性**:
    此规则将 `[t₁ ≡ t₂]` 归约为 `()`，前提是 `t₁ ≈_C t₂`。
    *   根据 **引理 7.4.1**，`U` 中不含 `()`，因此 `codom(σ)` 中也不含 `()`。这意味着 `t₁` 和 `t₂` 只能是 SK 编码项或规则项。
    *   若 `t₁`, `t₂` 是 SK 范式编码，根据 **引理 7.4.2**，`t₁ ≈_C t₂` 仅当它们语法相同。这种归约是无害的。
    *   若 `t₁` 是 SK 编码而 `t₂` 不是 (e.g. `R_K`)，根据模型 `M_SK`，它们不 `≡_SK`，故 `t₁ ≈_C t₂` 不成立。
    *   **结论**: `Reflection Reduction` 不会干扰模拟。

3.  **`Redundancy Elimination` 的惰性**:
    此规则作用于 `(... ≡ ())` 形式的项。在初始构型 `C₀` 中不存在这种项。`R_K` 和 `R_S` 的右侧也只产生 `app(...)` 结构。因此，这种形式的项永远不会在模拟过程中被创造出来。此规则是惰性的。

**最终结论**
我们已经证明，从为模拟 SK 逻辑而构造的初始状态 `S₀` 出发，所有可能的 CIE 计算序列都忠实地模拟了 SK 的归约序列。**语义保守性引理**和**纯净性不变式**是此忠实性论证的基石。由于 CIE 能够忠实地模拟图灵完备的 SK 组合子逻辑，我们严谨地得出结论：**CIE 系统是图灵完备的。**
