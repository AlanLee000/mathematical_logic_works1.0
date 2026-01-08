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

*   **形式化注记**: 在形式化证明中，所有关于元组记法的引理都必须在其底层的 `pair`/`unit` 表示上通过归纳进行证明。例如，可能需要首先证明编码函数 `E(·)` 的一些基本性质（如单射性：`E(l₁) = E(l₂) → l₁ = l₂`）。


**引理 1.4.1 (编码单射性)**
编码函数 `E(·)` 是单射的。即，对于任意项的有限列表 `l₁`, `l₂`，若 `E(l₁) = E(l₂)`，则 `l₁ = l₂`。

**证明.**
我们对 `l₁` 和 `l₂` 的结构进行同步归纳（a simultaneous structural induction）。这意味着我们需要考虑所有四种组合情况，基于每个列表是空列表 `[]` 还是非空列表 `h::t`。

*   **基础情形 1: `l₁ = []` 且 `l₂ = []`**
    *   前提 `E(l₁) = E(l₂)` 变为 `E([]) = E([])`，即 `() = ()`，此为真。
    *   结论 `l₁ = l₂` 变为 `[] = []`，此亦为真。
    *   因此，该情况得证。

*   **基础情形 2: `l₁ = h₁ :: t₁` 且 `l₂ = []`**
    *   前提 `E(l₁) = E(l₂)` 变为 `E(h₁ :: t₁) = E([])`。
    *   根据 `E` 的定义，这展开为 `pair(h₁, E(t₁)) = ()`。
    *   然而，在自由项代数 $T_\Sigma(V)$ 中，项的相等性是句法上的。一个由构造子 `pair` 生成的项永远不能等于一个由不同的构造子 `unit`（即`()`）生成的项。这被称为**“无混淆”性质 (no-confusion property)** of term algebras。
    *   因此，前提 `pair(h₁, E(t₁)) = ()` 是**假**的。
    *   在逻辑上，由假前提可以推出任何结论 (`ex falso quodlibet`)，故蕴含式 `False → l₁ = l₂` 是**空洞地为真 (vacuously true)**。
    *   因此，该情况得证。

*   **基础情形 3: `l₁ = []` 且 `l₂ = h₂ :: t₂`**
    *   此情况与基础情形2对称。前提 `E([]) = E(h₂ :: t₂)` 展开为 `() = pair(h₂, E(t₂))`，此为假。
    *   因此，该情况亦空洞地为真。

*   **归纳步骤: `l₁ = h₁ :: t₁` 且 `l₂ = h₂ :: t₂`**
    *   **归纳假设 (IH):** 我们假设对于结构上更小的列表 `t₁` 和 `t₂`，引理成立。即，`E(t₁) = E(t₂) → t₁ = t₂`。
    *   我们从当前情况的前提开始：`E(h₁ :: t₁) = E(h₂ :: t₂)`。
    *   根据 `E` 的定义，这展开为 `pair(h₁, E(t₁)) = pair(h₂, E(t₂))`。
    *   再次应用项代数的“无混淆”/单射性质，一个 `pair` 项等于另一个 `pair` 项，当且仅当它们的对应参数相等。由此可得两个等式：
        1.  `h₁ = h₂`
        2.  `E(t₁) = E(t₂)`
    *   现在，我们可以对等式 `E(t₁) = E(t₂)` 应用我们的**归纳假设 (IH)**。根据 IH，此等式蕴含 `t₁ = t₂`。
    *   结合 `h₁ = h₂` 和 `t₁ = t₂`，根据列表相等性的定义，我们得出 `h₁ :: t₁ = h₂ :: t₂`，即 `l₁ = l₂`。
    *   我们已经成功地从前提 `E(l₁) = E(l₂)` 推导出了结论 `l₁ = l₂`。
    *   因此，归纳步骤得证。

由于所有四种情况都已覆盖且得证，通过结构归纳，我们证明了编码函数 `E(·)` 是单射的。
**Q.E.D.**

##### **1.5. 变量、替换与核心元理论 (Variables, Substitution, and Core Meta-Theory)**

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

我们首先定义单点替换 $t[s/j]$，它表示在项 $t$ 中将所有出现的变量 $j$ 替换为项 $s$。
*   $n[s/j] := s$  如果 $n = j$
*   $n[s/j] := n$  如果 $n ≠ j$
*   $f(t₁, ..., tₖ)[s/j] := f(t₁[s/j], ..., tₖ[s/j])$

一个多点替换 $\theta$ 在项 $t$ 上的应用，记为 $\theta(t)$，被归纳定义为对 $\theta$ 定义域中所有变量的同时替换：
*   对于变量 $n$，$\theta(n)$ 定义为：
    *   $\theta[n]$ (即映射 $\theta$ 在键 $n$ 上的值)，如果 $n \in \mathrm{dom}(\theta)$
    *   $n$ 本身，如果 $n \notin \mathrm{dom}(\theta)$
*   $\theta(f(t₁, ..., tₖ)) := f(\theta(t₁), ..., \theta(tₖ))$

后续所有证明都**以以下关键引理的成立为前提**。这些引理构成了本系统元理论的基石，并在本节中被严格证明。

---
**引理 1.5.4 (替换的同态性 Substitution Homomorphism)**
对于任意函数符号 $f \in \Sigma$ 及其元数 $k$，任意项 $t_1, \dots, t_k, s$ 和任意变量 $j \in \mathbb{N}$，以下等式成立：
$$ f(t_1, \dots, t_k)[s/j] = f(t_1[s/j], \dots, t_k[s/j]) $$
**证明:**
此引理的成立直接源自单点替换（定义 1.5.3）的归纳定义第三条。等式两边在定义上完全相同。这是一个依据定义的直接证明，无需归纳。 **Q.E.D.**

---
**引理 1.5.5 (自由变量引理 - 单点替换 Free Variables Lemma for Single Substitution)**
对于任意项 $t$, $s$ 和任意变量 $j \in \mathbb{N}$，以下等式成立：
$$ \mathsf{vars}(t[s/j]) = \begin{cases} (\mathsf{vars}(t) \setminus \{j\}) \cup \mathsf{vars}(s) & \text{if } j \in \mathsf{vars}(t) \\ \mathsf{vars}(t) & \text{if } j \notin \mathsf{vars}(t) \end{cases} $$
**证明:**
我们对项 $t$ 的结构进行归纳。
*   **基础情形 (t = n):**
    *   $vars(n) = \{n\}$。
    *   **情况 a: $j = n$**。此时 $j ∈ vars(n)$。
        *   LHS: $vars(n[s/n]) = vars(s)$。
        *   RHS: $(vars(n) \setminus \{n\}) \cup vars(s) = (\{n\} \setminus \{n\}) \cup vars(s) = \emptyset \cup vars(s) = vars(s)$。等式成立。
    *   **情况 b: $j ≠ n$**。此时 $j \notin vars(n)$。
        *   LHS: $vars(n[s/j]) = vars(n) = \{n\}$。
        *   RHS: $vars(n) = \{n\}$。等式成立。
*   **归纳步骤 (t = f(t₁, ..., tₖ)):**
    *   **归纳假设 (IH):** 对所有 $i ∈ {1..k}$，引理对 $tᵢ$ 成立。
    *   $vars(t) = ⋃ᵢ vars(tᵢ)$。
    *   **情况 a: $j ∈ vars(t)$**。这意味着至少存在一个 $i$ 使得 $j ∈ vars(tᵢ)$。
        *   LHS: $vars(t[s/j]) = vars(f(t₁[s/j], ..., tₖ[s/j])) = ⋃ᵢ vars(tᵢ[s/j])$。
        *   应用归纳假设，我们将LHS的并集分为两部分：
            $LHS = (⋃_{i | j ∈ vars(tᵢ)} ((\mathsf{vars}(tᵢ) \setminus \{j\}) \cup \mathsf{vars}(s))) \cup (⋃_{i | j ∉ vars(tᵢ)} \mathsf{vars}(tᵢ))$。
        *   通过集合的分配律和结合律，上式可以重组。首先分配 `∪ vars(s)`：
            $LHS = (⋃_{i | j ∈ vars(tᵢ)} (\mathsf{vars}(tᵢ) \setminus \{j\})) \cup \mathsf{vars}(s) \cup (⋃_{i | j ∉ vars(tᵢ)} \mathsf{vars}(tᵢ))$
        *   合并两个不含 `vars(s)` 的并集：
            $LHS = (⋃ᵢ (\mathsf{vars}(tᵢ) \setminus \{j\})) \cup \mathsf{vars}(s)$
        *   利用 `(⋃Aᵢ) \ B = ⋃(Aᵢ \ B)` 的性质:
            $LHS = (\mathsf{vars}(t) \setminus \{j\}) \cup \mathsf{vars}(s)$。
        *   RHS: $(\mathsf{vars}(t) \setminus \{j\}) \cup \mathsf{vars}(s)$。LHS = RHS。
    *   **情况 b: $j \notin vars(t)$**。这意味着对所有 $i$，$j \notin vars(tᵢ)$。
        *   LHS: $vars(t[s/j]) = ⋃ᵢ vars(tᵢ[s/j])$。
        *   根据归纳假设，$vars(tᵢ[s/j]) = vars(tᵢ)$ 对所有 $i$ 成立。
        *   因此 $LHS = ⋃ᵢ vars(tᵢ) = vars(t)$。
        *   RHS: $vars(t)$。LHS = RHS。
**Q.E.D.**

---
**引理 1.5.6 (自由变量引理 - 多点替换 Free Variables Lemma for Simultaneous Substitution)**
对于任意项 $t$ 和任意替换 $\theta$，以下等式成立：
$$ \mathsf{vars}(\theta(t)) = (\mathsf{vars}(t) \setminus \mathrm{dom}(\theta)) \cup \bigcup_{j \in (\mathrm{dom}(\theta) \cap \mathsf{vars}(t))} \mathsf{vars}(\theta[j]) $$
**证明:**
我们对项 $t$ 的结构进行归纳。
*   **基础情形 (t = n):**
    *   **情况 a: $n \in \mathrm{dom}(\theta)$**。
        *   LHS: $\mathsf{vars}(\theta(n)) = \mathsf{vars}(\theta[n])$。
        *   RHS: $(\{n\} \setminus \mathrm{dom}(\theta)) \cup \bigcup_{j \in (\mathrm{dom}(\theta) \cap \{n\})} \mathsf{vars}(\theta[j]) = \emptyset \cup \mathsf{vars}(\theta[n]) = \mathsf{vars}(\theta[n])$。LHS = RHS。
    *   **情况 b: $n \notin \mathrm{dom}(\theta)$**。
        *   LHS: $\mathsf{vars}(\theta(n)) = \mathsf{vars}(n) = \{n\}$。
        *   RHS: $(\{n\} \setminus \mathrm{dom}(\theta)) \cup \emptyset = \{n\}$。LHS = RHS。
*   **归纳步骤 (t = f(t₁, ..., tₖ)):**
    *   **归纳假设 (IH):** 对所有 $i ∈ {1..k}$，引理对 $tᵢ$ 成立。
    *   LHS: $\mathsf{vars}(\theta(t)) = \mathsf{vars}(f(\theta(t_1), ..., \theta(t_k))) = \bigcup_i \mathsf{vars}(\theta(t_i))$。
    *   应用归纳假设：
        LHS = $\bigcup_i ((\mathsf{vars}(t_i) \setminus \mathrm{dom}(\theta)) \cup \bigcup_{j \in (\mathrm{dom}(\theta) \cap \mathsf{vars}(t_i))} \mathsf{vars}(\theta[j]))$
    *   通过集合的分配律重组：
        LHS = $(\bigcup_i (\mathsf{vars}(t_i) \setminus \mathrm{dom}(\theta))) \cup (\bigcup_i \bigcup_{j \in (\mathrm{dom}(\theta) \cap \mathsf{vars}(t_i))} \mathsf{vars}(\theta[j]))$
    *   简化第一部分：
        $(\bigcup_i \mathsf{vars}(t_i)) \setminus \mathrm{dom}(\theta) = \mathsf{vars}(t) \setminus \mathrm{dom}(\theta)$
    *   简化第二部分：
        $\bigcup_{j \in (\mathrm{dom}(\theta) \cap (\bigcup_i \mathsf{vars}(t_i)))} \mathsf{vars}(\theta[j]) = \bigcup_{j \in (\mathrm{dom}(\theta) \cap \mathsf{vars}(t))} \mathsf{vars}(\theta[j])$
    *   合并后，LHS 与 RHS 相等。
**Q.E.D.**

---
**辅助引理 1.5.7 (替换对无关变量的影响)**
若 $k \notin \mathsf{vars}(s₁)$，则对于任意项 $s_2$ 和变量 $j \neq k$，有 $s_1[s_2/k] = s_1$。
**证明:**
我们对项 $s_1$ 的结构进行归纳。
*   **基础情形 (s₁ = n):**
    *   前提 $k \notin vars(n)$ 意味着 $k \neq n$。
    *   $n[s_2/k]$: 因为 $n \neq k$，根据替换定义，结果为 $n$。所以 $s_1[s_2/k] = s_1$。
*   **归纳步骤 (s₁ = f(t₁, ..., tₘ)):**
    *   前提 $k \notin vars(s_1)$ 意味着对所有 $i$，$k \notin vars(t_i)$。
    *   $s_1[s_2/k] = f(t_1[s_2/k], \dots, t_m[s_2/k])$。
    *   根据归纳假设，由于对所有 $i$ 都有 $k \notin vars(t_i)$，因此 $t_i[s_2/k] = t_i$。
    *   所以 $s_1[s_2/k] = f(t_1, \dots, t_m) = s_1$。
**Q.E.D.**

---
**引理 1.5.8 (替换引理 Substitution Lemma)**
对于任意项 $t, s₁, s₂$ 和任意不同的变量 $j, k \in \mathbb{N}$，并且满足 $k \notin \mathsf{vars}(s₁)$ 和 $j \notin \mathsf{vars}(s_2)$，以下等式成立：
$$ (t[s₁/j])[s₂/k] = (t[s₂/k])[s₁/j] $$
**证明:**
我们对项 $t$ 的结构进行归纳。
*   **基础情形 (t = n):**
    *   **情况 a: $n = j$**:
        *   LHS = $(j[s₁/j])[s₂/k] = s₁[s₂/k]$。根据前提 $k \notin \mathsf{vars}(s₁)$ 和**辅助引理 1.5.7**，我们有 $s₁[s₂/k] = s₁$。所以 LHS = $s_1$。
        *   RHS = $(j[s₂/k])[s₁/j] = j[s₁/j] = s₁$ (因为 $j \neq k$)。
        *   LHS = RHS。
    *   **情况 b: $n = k$**:
        *   LHS = $(k[s₁/j])[s₂/k] = k[s₂/k] = s₂$ (因为 $j \neq k$)。
        *   RHS = $(k[s₂/k])[s₁/j] = s₂[s₁/j]$。根据前提 $j \notin \mathsf{vars}(s₂)$ 和**辅助引理 1.5.7**（变量互换），我们有 $s₂[s₁/j] = s₂$。所以 RHS = $s_2$。
        *   LHS = RHS。
    *   **情况 c: $n \neq j$ and $n \neq k$**: LHS = $(n[s₁/j])[s₂/k] = n[s₂/k] = n$。RHS = $(n[s₂/k])[s₁/j] = n[s₁/j] = n$。LHS = RHS。
*   **归纳步骤 (t = f(t₁, ..., tₘ)):**
    *   LHS: $(f(t_1, \dots, t_m)[s₁/j])[s₂/k] = f( (t_1[s₁/j])[s₂/k], \dots, (t_m[s₁/j])[s₂/k] )$
    *   RHS: $(f(t_1, \dots, t_m)[s₂/k])[s₁/j] = f( (t_1[s₂/k])[s₁/j], \dots, (t_m[s₂/k])[s₁/j] )$
    *   根据归纳假设，对所有 $i$ 都成立 $(t_i[s₁/j])[s₂/k] = (t_i[s₂/k])[s₁/j]$。因此，LHS = RHS。
**Q.E.D.**


##### **1.6. 形式化预备知识：位置与子项 (Formal Preliminaries: Positions and Subterms)**
为确保严谨性，我们形式化地定义项中的位置和相关操作。
*   **位置 (Positions)**: 一个项 $t$ 的位置集合 $\mathcal{P}os(t)$ 是一个由自然数序列组成的集合，定义如下：
    *   $\mathcal{P}os(x) := \{\epsilon\}$ (空序列代表根位置)。
    *   $\mathcal{P}os(f(t_1, \dots, t_n)) := \{\epsilon\} \cup \bigcup_{i=1}^n \{i \cdot p \mid p \in \mathcal{P}os(t_i)\}$ (其中 $·$ 表示序列连接)。
*   **子项提取 (Subterm Extraction)**: 对于一个项 $t$ 和一个**合法位置 $p \in \mathcal{P}os(t)$**，位于 $p$ 的子项记为 $t|_p$，其定义如下：
    *   $t|_\epsilon := t$。
    *   $f(t_1, \dots, t_n)|_{i \cdot p} := t_i|_p$ (其中 $p \in \mathcal{P}os(t_i)$)。
*   **子项集合 (Set of Subterms)**: 项 $t$ 的子项集合 $\mathsf{Sub}(t)$ 定义为 $\{t|_p \mid p \in \mathcal{P}os(t)\}$。
*   **位置替换 (Replacement at Position)**: 将项 $t$ 在一个**合法位置 $p \in \mathcal{P}os(t)$** 的子项替换为项 $s$，记为 $t[s]_p$，其定义如下：
    *   $t[s]_\epsilon := s$。
    *   $f(t_1, \dots, t_n)[s]_{i \cdot p} := f(t_1, \dots, t_i[s]_p, \dots, t_n)$ (其中 $p \in \mathcal{P}os(t_i)$)。

*   **形式化注记**: 在形式化实现中，$t|_p$ 和 $t[s]_p$ 是偏函数，其合法性都必须以 $p \in \mathcal{P}os(t)$ 作为前提。这通常通过使用依赖类型（函数的类型签名包含前提 `p ∈ Pos(t)`）或返回一个 `option` 类型（对于非法位置返回 `None`）来处理。需要证明相关函数在此前提下是全定义的（total），并且满足其代数性质（例如 $t[t|_p]_p = t$）。


---

### **2. 证明论层 (Proof-Theoretic Layer)**

该层定义了理想化的可证等价关系 `~`。

#### **2.1. 判断与相继 (Judgements and Sequents)**
*   **等价判断 (Equivalence Judgement)** 的形式为 $t_1 \sim t_2$，表示项 $t_1$ 与 $t_2$ 等价。
*   **上下文 (Context)** $\Gamma$ 是一个有限的等价判断**多重集 (multiset)**。
*   **相继 (Sequent)** 的形式为 $\Gamma \vdash t_1 \sim t_2$，表示在上下文 $\Gamma$ 的假设下，可以证明 $t_1$ 与 $t_2$ 等价。
*   **形式化注记**: 我们将上下文 `Γ` 定义为多重集，以准确反映假设的顺序无关性。在Coq或Lean等证明助手中，多重集通常通过列表加上一个置换等价关系（`Permutation`）来形式化，或者使用专门的多重集库。这种选择意味着所有推理规则在逻辑上都隐式地满足交换规则（Exchange Rule），无需将其作为一条独立的规则来证明。

##### **2.1.1. 上下文的句法角色 (Syntactic Role of Contexts)**
在本形式系统中，上下文 `Γ` 中的判断根据其是否包含变量，在推理规则中扮演不同的句法角色：

1.  **公理模式 (Axiom Schema)**: 如果一个判断 `(l ~ r)` 出现在 `Γ` 中且 `vars(l) ∪ vars(r) ≠ ∅`，则该判断被视为一个公理模式。它只能被 **(Hyp-Schema)** 规则使用，该规则允许对其进行任意替换。
2.  **局部公理 (Local Axiom)**: 如果一个判断 `(l ~ r)` 出现在 `Γ` 中且 `l` 和 `r` 都是基项，则它被视为一个局部公理。它只能被 **(Hyp-Local)** 规则使用，该规则仅允许将其作为结论直接引入。

##### **2.1.2. 上下文的动态来源 (Dynamic Origin of Contexts)**
在操作语义（第3节）中，上下文 `Γ` 是从一个构型项 `C` 中动态提取的，`C` 中所有形如 `[l ≡ r]` 的子项都会贡献一个判断 `(l ~ r)` 到 `Γ(C)` 中。

#### **2.2. 推理规则 (Inference Rules)**

##### A. 结构规则 (Structural Rules)
*   **(Refl)**: $\dfrac{}{\Gamma \vdash t \sim t}$
*   **(Sym)**: $\dfrac{\Gamma \vdash t_1 \sim t_2}{\Gamma \vdash t_2 \sim t_1}$
*   **(Trans)**: $\dfrac{\Gamma \vdash t_1 \sim t_2 \quad \Gamma \vdash t_2 \sim t_3}{\Gamma \vdash t_1 \sim t_3}$

##### B. 同余规则 (Congruence Rule)
*   **(Cong)**: 对任意 $n$-元 $f \in \Sigma$，$\dfrac{\Gamma \vdash t_1 \sim s_1 \quad \dots \quad \Gamma \vdash t_n \sim s_n}{\Gamma \vdash f(t_1,\dots,t_n) \sim f(s_1,\dots,s_n)}$

##### C. 假设规则 (Hypothesis Rules) 
*   **(Hyp-Schema)**: 若判断 $(l \sim r)$ 出现在 $\Gamma$ 中，且 $\mathsf{vars}(l) \cup \mathsf{vars}(r) \neq \emptyset$，对于任意替换 $\theta: V \to T_\Sigma(V)$，则：
    $\dfrac{}{\Gamma \vdash \theta(l) \sim \theta(r)}$
*   **(Hyp-Local)**: 若判断 $(l \sim r)$ 出现在 $\Gamma$ 中，且 $\mathsf{vars}(l) \cup \mathsf{vars}(r) = \emptyset$，则：
    $\dfrac{}{\Gamma \vdash l \sim r}$


##### D. 等价内化规则 (Equivalence Internalization Rules)
*   **(Equiv-Intro)**: $\dfrac{\Gamma, t_1 \sim t_2 \;\vdash\; s_1 \sim s_2 \qquad \Gamma, s_1 \sim s_2 \;\vdash\; t_1 \sim t_2}{\Gamma \vdash (t_1 \equiv t_2) \sim (s_1 \equiv s_2)}$
(其中 `Γ, A` 表示将判断 `A` 添加到多重集 `Γ` 中，即多重集并集 `Γ ∪ {A}`。)
*   **(Equiv-Elim)**: $\dfrac{\Gamma \vdash (t_1 \equiv t_2) \sim ()}{\Gamma \vdash t_1 \sim t_2}$
*   **(Equiv-Reflection)**: $\dfrac{\Gamma \vdash t_1 \sim t_2}{\Gamma \vdash (t_1 \equiv t_2) \sim ()}$

##### E. 具体化规则 (Reification Rule)
此规则建立了一个项与其自身真值断言之间的根本等价关系。
*   **(Reif)**: $\dfrac{}{\Gamma \vdash t \sim (t \equiv ())}$

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

**证明:**
我们对项 $C$ 的结构进行归纳。
*   **基础情形 ($C$ 是变量 $v$):**
    *   $\mathsf{ExtractGroundTerms}(v) = \emptyset$。$v$ 没有基项子项。两个性质均平凡成立。
*   **归纳步骤 ($C = f(t_1, \dots, t_n)$):**
    *   **归纳假设 (IH):** 对所有 $i \in \{1, \dots, n\}$，引理对 $t_i$ 成立。
    *   **情况 a ($C$ 是基项):**
        *   $\mathsf{ExtractGroundTerms}(C) = (\bigcup_{i=1}^n \mathsf{ExtractGroundTerms}(t_i)) \cup \{C\}$。
        *   (证明性质1) "$\Rightarrow$": 设 $g \in \mathsf{ExtractGroundTerms}(C)$。要么 $g=C$，此时 $g$ 是 $C$ 的基项子项；要么 $g \in \mathsf{ExtractGroundTerms}(t_i)$ 之一。根据IH，$g$ 是 $t_i$ 的基项子项，因此也是 $C$ 的基项子项。
        *   "$\Leftarrow$": 设 $g$ 是 $C$ 的基项子项。要么 $g=C$，此时 $g \in \{C\}$；要么 $g$ 是某个 $t_i$ 的子项。由于 $C$ 是基项，所有 $t_i$ 也是基项，因此 $g$ 是 $t_i$ 的基项子项。根据IH，$g \in \mathsf{ExtractGroundTerms}(t_i)$。两种情况都可推出 $g \in \mathsf{ExtractGroundTerms}(C)$。
        *   (证明性质2) 如果 `()` 不是 $C$ 的子项，那么 `()` $\neq C$，且 `()` 也不是任何 $t_i$ 的子项。根据IH，`()` $\notin \mathsf{ExtractGroundTerms}(t_i)$ 对所有 $i$ 成立。因此 `()` 不在并集中。性质2成立。
    *   **情况 b ($C$ 含有变量):**
        *   $\mathsf{ExtractGroundTerms}(C) = \bigcup_{i=1}^n \mathsf{ExtractGroundTerms}(t_i)$。
        *   证明与情况a类似，但由于 $C$ 本身不被加入集合，论证更直接。
通过归纳法，引理得证。 **Q.E.D.**


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

**引理 3.3.2.1 (E_C 计算的正确性)**
算法 `Compute_EC(C, U)` 的输出集合在集合相等意义下等于声明式定义的 $E_C$。

**证明.**
我们将从两个方向证明集合相等性。
1.  **可靠性 (Soundness): `Compute_EC(C, U) ⊆ E_C`**
    *   设 `(t₁, t₂)` 是由 `Compute_EC` 算法生成的任意一个元素。
    *   根据算法步骤 2.b.iii，必然存在一个 `(l,r) ∈ Γ(C)` 和一个替换 `σ ∈ S_{V_l, U}` (即 `σ` 是一个从 `vars(l)` 到 `U` 的替换)，使得 `t₁ = σ(l)` 且 `t₂ = σ(r)`。
    *   这完全符合声明式定义中元素的形式。因此，`(t₁, t₂) ∈ E_C`。
    *   由于 `(t₁, t₂)` 是任意选择的，我们得出 `Compute_EC(C, U) ⊆ E_C`。

2.  **完备性 (Completeness): `E_C ⊆ Compute_EC(C, U)`**
    *   设 `(t₁, t₂)` 是声明式定义的 `E_C` 中的任意一个元素。
    *   根据定义，必然存在一个 `(l,r) ∈ Γ(C)` 和一个从 `vars(l)` 到 `U` 的替换 `σ`，使得 `t₁ = σ(l)` 且 `t₂ = σ(r)`。
    *   现在我们考察 `Compute_EC` 算法。在步骤 2 中，它会迭代到这个特定的 `(l,r)`。
    *   在步骤 2.b.ii 中，算法会生成所有可能的从 `vars(l)` 到 `U` 的替换集合 `S_{vars(l), U}`。我们在此使用的替换 `σ` 正是这个集合中的一个元素。
    *   因此，在步骤 2.b.iii 的迭代中，算法必然会处理到这个 `σ`，计算出 `σ(l)` 和 `σ(r)`，并将序对 `(σ(l), σ(r))`，即 `(t₁, t₂)`，加入其输出集合中。
    *   由于 `(t₁, t₂)` 是任意选择的，我们得出 `E_C ⊆ Compute_EC(C, U)`。

结合可靠性和完备性，我们证明了两个集合相等。 **Q.E.D.**

*   **形式化注记**: $E_C$ 的计算过程正确地实现了其声明式定义。需要注意的是，步骤 2.b.ii 中生成的替换集合的大小是 $|U|^{|\mathsf{vars}(l)|}$，相对于 `U` 的大小和 `l` 中变量的数量是指数级的。这表明 `≈_C` 的判定算法虽然理论上存在，但复杂度很高。在形式化证明中，应尽可能避免直接展开 `E_C` 的定义，而是利用其抽象性质进行推理。

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

**引理 4.2.1 (状态的可判定相等性)**
存在一个可计算函数 `beq_state: State × State → bool`，可以判定任意两个状态 `S₁` 和 `S₂` 的相等性，即对于任意 `S₁, S₂`，`beq_state(S₁, S₂) = true` 当且仅当 `S₁ = S₂`。

**证明.**
我们将通过自底向上地为系统的每个句法结构构造一个布尔相等函数，并证明其正确性，来构造性地证明此引理。

1.  **基础组件的可判定相等性**:
    *   **变量 (`V = ℕ`):** 自然数的相等性是可判定的。存在一个函数 `beq_nat(n₁, n₂) : bool`，其满足 `beq_nat(n₁, n₂) = true ↔ n₁ = n₂`。
    *   **函数符号 (`f ∈ Σ`):** 由于签名 `Σ` 是一个预先固定的有限集合，其元素的相等性是可判定的。存在一个函数 `beq_symbol(f, g) : bool`，满足 `beq_symbol(f, g) = true ↔ f = g`。

2.  **项的可判定相等性**:
    我们归纳地定义一个函数 `beq_term(t₁, t₂) : bool` 如下：
    *   若 `t₁` 是变量 `n₁` 且 `t₂` 是变量 `n₂`，则返回 `beq_nat(n₁, n₂)`.
    *   若 `t₁ = f(a₁,...,aₖ)` 且 `t₂ = g(b₁,...,bₘ)`，则返回：
        `beq_symbol(f, g) ∧ (k = m) ∧ beq_termlist([a₁,...,aₖ], [b₁,...,bₘ])`
        其中 `beq_termlist` 递归地对两个项列表的对应元素调用 `beq_term`，并返回所有结果的逻辑与。
    *   在所有其他情况（例如，一个变量与一个函数应用比较），返回 `false`。

    **正确性证明 (`beq_term(t₁, t₂) = true ↔ t₁ = t₂`)**:
    我们对 `t₁` 和 `t₂` 的结构进行同步归纳。
    *   **⇒ (可靠性):** 假设 `beq_term(t₁, t₂) = true`。
        *   若 `t₁, t₂` 是变量，则 `beq_nat` 返回 `true`，故 `n₁ = n₂`，因此 `t₁ = t₂`。
        *   若 `t₁, t₂` 是函数应用，则 `f=g`, `k=m`，且对所有 `i`, `beq_term(aᵢ, bᵢ) = true`。根据归纳假设，`aᵢ = bᵢ` 对所有 `i` 成立。因此 `f(a₁,...,aₖ) = g(b₁,...,bₘ)`，即 `t₁ = t₂`。
    *   **⇐ (完备性):** 假设 `t₁ = t₂`。我们对 `t₁` 的结构进行归纳。
        *   若 `t₁` 是变量 `n`，则 `t₂` 也是 `n`。`beq_term(n, n)` 调用 `beq_nat(n, n)`，返回 `true`。
        *   若 `t₁` 是 `f(a₁,...,aₖ)`，则 `t₂` 也是 `f(a₁,...,aₖ)`。`beq_term` 的调用将比较 `f` 和 `f`（`true`），`k` 和 `k`（`true`），并对相同的子项列表 `[a₁...],[a₁...]` 调用 `beq_termlist`。根据归纳假设，`beq_term(aᵢ, aᵢ)` 对所有 `i` 返回 `true`，因此最终结果为 `true`。

3.  **项的有限集的可判定相等性**:
    我们将有限集 `U` 表示为无重复元素的列表。
    *   首先定义列表成员函数 `is_elem(t, L) : bool`，它通过对列表 `L` 进行线性扫描，并使用 `beq_term` 比较 `t` 与每个元素，来判定 `t` 是否在 `L` 中。其正确性 `is_elem(t, L) = true ↔ t ∈ L` 直接源于 `beq_term` 的正确性。
    *   然后定义子集函数 `is_subset(L₁, L₂) : bool`，它检查 `L₁` 中的每个元素是否都在 `L₂` 中（使用 `is_elem`）。
    *   最后定义集合相等函数 `beq_set_term(U₁, U₂) : bool` (以列表 `L₁, L₂` 为代表)，其值为 `is_subset(L₁, L₂) ∧ is_subset(L₂, L₁)`。

    **正确性证明 (`beq_set_term(U₁, U₂) = true ↔ U₁ = U₂`)**:
    这直接源于集合相等的定义（两个集合相等当且仅当它们互为子集）以及 `is_subset` 和 `is_elem` 函数已被证明的正确性。

4.  **状态的可判定相等性**:
    对于两个状态 `S₁ = ⟨C₁, U₁⟩` 和 `S₂ = ⟨C₂, U₂⟩`，我们定义 `beq_state(S₁, S₂) : bool` 如下：
    `beq_state(S₁, S₂) := beq_term(C₁, C₂) ∧ beq_set_term(U₁, U₂)`

    **正确性证明 (`beq_state(S₁, S₂) = true ↔ S₁ = S₂`)**:
    根据序对相等的定义，`⟨C₁, U₁⟩ = ⟨C₂, U₂⟩` 当且仅当 `C₁ = C₂` 且 `U₁ = U₂`。
    *   **⇒:** 若 `beq_state` 返回 `true`，则 `beq_term(C₁, C₂) = true` 且 `beq_set_term(U₁, U₂) = true`。根据前面已证的正确性，这蕴含 `C₁ = C₂` 且 `U₁ = U₂`。因此 `S₁ = S₂`。
    *   **⇐:** 若 `S₁ = S₂`，则 `C₁ = C₂` 且 `U₁ = U₂`。根据前面已证的正确性，`beq_term(C₁, C₂)` 返回 `true` 且 `beq_set_term(U₁, U₂)` 返回 `true`。因此 `beq_state` 返回 `true`。

至此，我们已经成功构造了可计算函数 `beq_state` 并证明了其正确性。因此，状态的相等性是可判定的。
**Q.E.D.**

一个状态 $S_n$ 被称为一个**范式**，当且仅当不存在任何**不同于** $S_n$ 的状态 $S'$ 使得 $S_n \longrightarrow S'$ 成立。

形式化地，$S_n$ 是范式当且仅当集合 $\{S' \mid S_n \longrightarrow S' \land \text{beq\_state}(S_n, S') = \text{false} \}$ 为空。

#### **4.3. 基本性质 (Fundamental Properties)**

本节将阐述系统的一些关键性质，以证明其理论上的健全性。

##### **4.3.1. 定理 (良构性不变性)**

**本证明以第 1.5 节中已证明的核心元理论引理的成立为前提。**

*   **证明**: 归约规则只会在构型项中替换或引入基项。对于**模式应用 (Schema Application)** 规则，引入的项是 $σ(r)$。根据规则前提，$σ$ 的值域 $codom(σ)$ 是 $U$ 的子集，因此 $σ$ 是一个基项替换。根据良构性约束 $vars(r) ⊆ vars(l)$，$r$ 中的所有变量也都在 $l$ 中，即在 $dom(σ)$ 中。
    根据在 **第1.5节** 已证明的 **自由变量引理 - 多点替换 (引理 1.5.6)**，我们有 $vars(σ(r)) = (vars(r) \setminus \mathrm{dom}(σ)) \cup \bigcup_{j \in (\mathrm{dom}(σ) \cap vars(r))} vars(σ[j])$。
    由于 $vars(r) ⊆ \mathrm{dom}(σ)$，第一项 `(vars(r) \ dom(σ))` 为空集。由于 $σ$ 是一个基项替换，其 codomain 中的所有项都是基项，因此对于任何变量 `j`，$vars(σ[j]) = ∅$。这意味着第二部分的并集也是空集。故 $vars(σ(r)) = ∅$，即 $σ(r)$ 是一个基项。
    其他规则引入的也是基项 $()$ 或已存在的子项 $(t_1 ≡ t_2)$。因此，没有新的带变量的 $(l ≡ r)$ 子项被引入，良构性得以保持。


##### **4.3.2. 定理 (操作语义的可靠性 Soundness)**
操作语义对于证明论语义是可靠的。即，若 $S = \langle C, U \rangle \longrightarrow S' = \langle C', U' \rangle$，则在上下文 $\Gamma(C)$ 下可证 $C \sim C'$，即 $\Gamma(C) \vdash C \sim C'$。

###### **引理：操作同余的提升 (Lifting Operational Congruence)**
对于任何状态 $S = \langle C, U \rangle$，以及任意两个基项 $t_1, t_2 \in T_\Sigma$，如果 $t_1 \approx_C t_2$，那么 $\Gamma(C) \vdash t_1 \sim t_2$。

**证明**: 对 $t_1 \approx_C t_2$ 的推导结构进行归纳（基于第3.3节的定义）。

1.  **基础情形 (Base)**: $(t_1, t_2) \in E_C$。根据 $E_C$ 的定义，存在一个判断 $(l \sim r)$ 在 $\Gamma(C)$ 中和一个基项替换 $\sigma: \mathsf{vars}(l) \to U$，使得 $t_1 = \sigma(l)$ 且 $t_2 = \sigma(r)$。
    *   **情况a (源于公理模式)**: `vars(l) ∪ vars(r) ≠ ∅`。应用 **(Hyp-Schema)** 规则，可得 $\Gamma(C) \vdash \sigma(l) \sim \sigma(r)$。
    *   **情况b (源于局部公理)**: `vars(l) ∪ vars(r) = ∅`。此时 $\sigma$ 为空替换，$l=t_1, r=t_2$。应用 **(Hyp-Local)** 规则，可得 $\Gamma(C) \vdash t_1 \sim t_2$。
    结论成立。

2.  **归纳步骤**: 假设对于所有推导高度小于 $h$ 的判断 $a \approx_C b$，结论 $\Gamma(C) \vdash a \sim b$ 均成立（归纳假设）。考虑一个推导高度为 $h$ 的判断 $t_1 \approx_C t_2$。其推导树的根节点必然是应用了 (Refl), (Sym), (Trans), 或 (Cong) 规则。
    *   **(Refl)**: $t_1 = t_2$。在证明系统中，规则 **(Refl)** 直接给出 $\Gamma(C) \vdash t_1 \sim t_1$。
    *   **(Sym)**: 该判断由一个高度更低的推导 $t_2 \approx_C t_1$ 生成。根据归纳假设，$\Gamma(C) \vdash t_2 \sim t_1$。应用 **(Sym)** 规则，得 $\Gamma(C) \vdash t_1 \sim t_2$。
    *   **(Trans)**: 该判断由两个高度更低的推导 $t_1 \approx_C t_3$ 和 $t_3 \approx_C t_2$ 生成。根据归纳假设，$\Gamma(C) \vdash t_1 \sim t_3$ 和 $\Gamma(C) \vdash t_3 \sim t_2$。应用 **(Trans)** 规则，得 $\Gamma(C) \vdash t_1 \sim t_2$。
    *   **(Cong)**: $t_1 = f(a_1, \dots, a_n)$ 且 $t_2 = f(b_1, \dots, b_n)$，且该判断由 $n$ 个高度更低的推导 $a_i \approx_C b_i$ 生成。根据归纳假设，$\Gamma(C) \vdash a_i \sim b_i$ 对所有 $i$ 成立。应用 **(Cong)** 规则，得 $\Gamma(C) \vdash f(a_1,\dots,a_n) \sim f(b_1,\dots,b_n)$。

通过数学归纳法，引理得证。
**Q.E.D.**

---

###### **定理 4.3.2 (操作语义的可靠性 Soundness)**

若 $S = \langle C, U \rangle \longrightarrow S' = \langle C', U' \rangle$，则 $\Gamma(C) \vdash C \sim C'$。

**证明**:
我们将对三条归约规则进行逐一分析。令 $\Gamma = \Gamma(C)$。根据同余规则 **(Cong)**，我们只需证明被重写的子项在上下文 $\Gamma$ 中与替换它的新项是可证等价的。

1.  **反射归约 (Reflection Reduction)**
    *   **前提**: 存在位置 $p$ 使得 $C|_p = (t_1 \equiv t_2)$，其中 $t_1, t_2 \in T_\Sigma$ 且 $t_1 \approx_C t_2$。
    *   **变换**: $C' = C[()]_{p}$。
    *   **证明**: 我们需要证明 $\Gamma \vdash (t_1 \equiv t_2) \sim ()$。
        1.  根据归约规则的前提，我们有 $t_1 \approx_C t_2$。
        2.  应用我们刚刚证明的 **引理 (操作同余的提升)**，可得 $\Gamma \vdash t_1 \sim t_2$。
        3.  对 $\Gamma \vdash t_1 \sim t_2$ 应用 **(Equiv-Reflection)** 规则，可得 $\Gamma \vdash (t_1 \equiv t_2) \sim ()$。
    *   此分项证明完成。

2.  **模式应用 (Schema Application)**
    *   **前提**: 存在位置 $p_{app}$ 使得 $C|_{p_{app}} = a$ 是一个基项，且存在一个公理模式 $(l \equiv r) = C|_{p_{ax}}$（即 $(l \sim r) \in \Gamma$），以及一个替换 $\sigma$ 使得 $a \approx_C \sigma(l)$。
    *   **变换**: $C' = C[\sigma(r)]_{p_{app}}$。
    *   **证明**: 我们需要证明 $\Gamma \vdash a \sim \sigma(r)$。
        1.  根据归约规则的前提，我们有 $(l \sim r) \in \Gamma$。应用 **(Hyp-Schema)** 规则，我们有 $\Gamma \vdash \sigma(l) \sim \sigma(r)$。 (I)
        2.  根据归约规则的前提，我们有 $a \approx_C \sigma(l)$。
        3.  应用 **引理 (操作同余的提升)**，可得 $\Gamma \vdash a \sim \sigma(l)$。 (II)
        4.  现在我们有两个可证判断：(II) $\Gamma \vdash a \sim \sigma(l)$ 和 (I) $\Gamma \vdash \sigma(l) \sim \sigma(r)$。
        5.  应用 **(Trans)** 规则，我们得到 $\Gamma \vdash a \sim \sigma(r)$。
    *   此分项证明完成。

3.  **冗余消除 (Redundancy Elimination)**
    *   **前提**: 存在位置 $p$ 使得 $C|_p = ((t_1 \equiv t_2) \equiv ())$。
    *   **变换**: $C' = C[(t_1 \equiv t_2)]_{p}$。
    *   **证明**: 我们需要证明 $\Gamma \vdash ((t_1 \equiv t_2) \equiv ()) \sim (t_1 \equiv t_2)$。
        1.  令项 $A = (t_1 \equiv t_2)$。我们需要证明 $\Gamma \vdash (A \equiv ()) \sim A$。
        2.  根据 **(Reif)** 规则，它是一个公理模式，对于任何项（包括 $A$）都成立：$\Gamma \vdash A \sim (A \equiv ())$。
        3.  对上述判断应用 **(Sym)** 规则，我们立即得到 $\Gamma \vdash (A \equiv ()) \sim A$。
    *   此分项证明完成。

由于所有三种归约规则都在证明论语义下保持了项的等价性，我们得出结论：若 $S \longrightarrow S'$，则 $\Gamma(C) \vdash C \sim C'$。

**Q.E.D.**

---
##### **4.3.3. 定理：核心逻辑规则的独立性**

本节旨在严格证明系统的三条核心逻辑规则——`(Reif)`、`(Equiv-Elim)` 和 `(Equiv-Reflection)`——是相互独立的。这意味着任何一条规则都不能由系统中的其他规则推导出来。我们将通过为每条规则构造一个语义模型来证明这一点，在该模型中，目标规则失效，而所有其他规则（包括结构规则和同余规则）均保持有效。

为简洁起见，我们假设所有模型都满足结构规则和同余规则的有效性，因为它们的有效性直接源于模型中等价关系的性质和函数解释的同态性。我们将重点验证核心逻辑规则。

---
###### **引理 4.3.3.1 (`(Reif)` 的独立性)**
规则 `(Reif)` 不能由 CIE 的其他规则推导出来。

**证明.**
我们构造一个三值逻辑模型 `M₁`：

1.  **域 (Domain):** $D = \{\top, \bot, \delta\}$，其中 `⊤` 代表“真/已定义”，`⊥` 代表“假”，`δ` 代表“数据”。
2.  **解释函数 (Interpretation)** $〚·〛_{M₁}$:
    *   $〚()〛 := \top$
    *   $〚\text{pair}(t_1, t_2)〛 := \delta$
    *   $〚f(...)〛 := \delta$ (对于任何其他非 `equiv` 的函数符号 $f$)
    *   $〚[t_1 \equiv t_2]〛 := \begin{cases} \top & \text{若 } 〚t_1〛 = 〚t_2〛 \\ \bot & \text{否则} \end{cases}$

现在我们验证规则的有效性：

*   **`(Reif)` 失效**:
    规则 `Γ ⊢ t ~ (t ≡ ())` 要求对任意项 `t` 和估值 `ν`，`〚t〛 = 〚[t ≡ ()]〛` 成立。
    考虑项 `t = pair((), ())`。
    *   LHS: $〚\text{pair}((), ())〛 = \delta$。
    *   RHS: $〚[\text{pair}((), ()) \equiv ()]〛$。由于 $〚\text{pair}((), ())〛 = \delta$ 且 $〚()〛 = \top$，两者不相等，因此 RHS 的解释为 $\bot$。
    *   等式 `δ = ⊥` 不成立。因此，`(Reif)` 规则在模型 `M₁` 中无效。

*   **`(Equiv-Elim)` 有效**:
    规则 `Γ ⊢ (t₁ ≡ t₂) ~ ()` ⇒ `Γ ⊢ t₁ ~ t₂`。
    语义上，若 `〚[t₁ ≡ t₂]〛 = 〚()〛`，则 `〚t₁〛 = 〚t₂〛`。
    前提 `〚[t₁ ≡ t₂]〛 = ⊤`。根据 `≡` 在 `M₁` 中的解释，这当且仅当 `〚t₁〛 = 〚t₂〛`。这正是结论。因此，规则有效。

*   **`(Equiv-Reflection)` 有效**:
    规则 `Γ ⊢ t₁ ~ t₂` ⇒ `Γ ⊢ (t₁ ≡ t₂) ~ ()`。
    语义上，若 `〚t₁〛 = 〚t₂〛`，则 `〚[t₁ ≡ t₂]〛 = 〚()〛`。
    前提 `〚t₁〛 = 〚t₂〛`。根据 `≡` 在 `M₁` 中的解释，这立即得出 `〚[t₁ ≡ t₂]〛 = ⊤`。而 `〚()〛` 也为 `⊤`。结论成立。因此，规则有效。

由于存在一个模型 `M₁` 使 `(Reif)` 失效而其他核心规则有效，`(Reif)` 是独立的。 **Q.E.D.**

###### 引理 4.3.3.2（(Equiv-reflection)的独立性）

**模型 `M_broken_reflection`**

这个模型的目标是使 `(Equiv-Reflection)` 失效，同时保持 `(Reif)` 和 `(Equiv-Elim)` 有效。

核心思想是引入一个“特权”真值和一个“非特权”数据值。`equiv` 操作被设计成只有当其参数都等于那个特权真值时，才会返回真值；在其他自相等的情况下，它会返回非特权值本身。

**1. 模型定义**

*   **域 (Domain):** 我们使用一个最简化的双值域：
    $D = \{ \mathbf{T}, \mathbf{D} \}$
    其中：
    *   $\mathbf{T}$ 代表 “真” (Truth)，是我们的“特权”值。
    *   $\mathbf{D}$ 代表 “数据” (Data)，是我们的“非特权”值。

*   **解释函数 (Interpretation)** $〚·〛$:
    1.  $〚()〛 := \mathbf{T}$
    2.  $〚\text{pair}(...)〛 := \mathbf{D}$ (以及所有其他数据构造)
    3.  $〚[t_1 \equiv t_2]〛$ 的解释由一个函数 $f_{equiv}: D \times D \to D$ 给出，其定义如下（可以视为一个 $2 \times 2$ 的表格）：

| $f_{equiv}$ | $\mathbf{T}$ | $\mathbf{D}$ |
| :---------: | :----------: | :----------: |
| $\mathbf{T}$ |   $\mathbf{T}$   |   $\mathbf{D}$   |
| $\mathbf{D}$ |   $\mathbf{D}$   |   $\mathbf{D}$   |

        这个函数可以描述为：`f_equiv(a,b)` 只有在 `a=b=T` 时才返回 `T`；否则返回 `D`。

**2. 规则有效性验证**

**(Reif) 有效**
我们需要证明 `〚t〛 = 〚[t ≡ ()]〛` 对任意项 `t` 成立。设 `v = 〚t〛`，这等价于证明 `v = f_{equiv}(v, 〚()〛) = f_{equiv}(v, \mathbf{T})` 对所有 `v \in D` 成立。

*   **情形 1: `v = T`**
    *   LHS = $\mathbf{T}$
    *   RHS = $f_{equiv}(\mathbf{T}, \mathbf{T})$。查阅表格，结果为 $\mathbf{T}$。
    *   $\mathbf{T} = \mathbf{T}$，成立。

*   **情形 2: `v = D`**
    *   LHS = $\mathbf{D}$
    *   RHS = $f_{equiv}(\mathbf{D}, \mathbf{T})$。查阅表格，结果为 $\mathbf{D}$。
    *   $\mathbf{D} = \mathbf{D}$，成立。

由于所有情况都成立，`(Reif)` 在此模型中是有效的。

**(Equiv-Elim) 有效**
我们需要证明：若 `〚[t₁ ≡ t₂]〛 = 〚()〛`，则 `〚t₁〛 = 〚t₂〛`。这在语义上等价于证明：若 $f_{equiv}(a, b) = \mathbf{T}$，则 $a = b$。

*   我们检查 $f_{equiv}$ 的定义表。
*   唯一能使 $f_{equiv}$ 返回 $\mathbf{T}$ 的情况是当两个参数都为 $\mathbf{T}$ 时，即 $a = \mathbf{T}$ 且 $b = \mathbf{T}$。
*   在这种情况下，结论 $a = b$ 显然成立。
*   在所有其他情况下，$f_{equiv}$ 的结果都不是 $\mathbf{T}$，因此蕴含式的前提为假，整个蕴含式空洞地为真。

因此，`(Equiv-Elim)` 在此模型中是有效的。

**(Equiv-Reflection) 失效**
我们需要构造一个反例，即找到两个项 `t₁` 和 `t₂`，使得 `〚t₁〛 = 〚t₂〛` 成立，但 `〚[t₁ ≡ t₂]〛 ≠ 〚()〛`。

*   **选择反例项**:
    *   令 `t₁ := pair()`
    *   令 `t₂ := pair()`

*   **验证其解释**:
    *   `〚t₁〛 = 〚pair()〛 = \mathbf{D}`
    *   `〚t₂〛 = 〚pair()㛗 = \mathbf{D}`
    *   前提 `〚t₁〛 = 〚t₂〛` 成立，因为 $\mathbf{D} = \mathbf{D}$。

*   **验证结论**: 我们需要检查 `〚[t₁ ≡ t₂]〛 = 〚()〛` 是否成立。
    *   LHS = `〚[pair() ≡ pair()]〛 = f_{equiv}(\mathbf{D}, \mathbf{D})`。
    *   查阅表格，`f_{equiv}(\mathbf{D}, \mathbf{D})` 的结果是 $\mathbf{D}$。
    *   RHS = `〚()〛 = \mathbf{T}`。
    *   结论要求 $\mathbf{D} = \mathbf{T}$，这显然是不成立的。

*   **结论**:
    我们找到了一个情况，其中规则的前提 (`pair() ~ pair()`) 在模型中成立，但其结论 (`(pair() ≡ pair()) ~ ()`) 在模型中不成立。
    因此，`(Equiv-Reflection)` 规则在此模型中是**无效的**。

---
**总结**
模型 `M_broken_reflection` 成功地展示了 `(Equiv-Reflection)` 相对于 `(Reif)` 和 `(Equiv-Elim)` 的独立性。这个模型揭示了一个深刻的特性：CIE 的 `(Reif)` 和 `(Equiv-Elim)` 规则并不足以强制 `equiv` 操作符成为一个普适的相等性检查器。它们只保证了与“真”值 `()` 相关的相等性行为是标准的，但为其他值的自相等性留下了非标准解释的空间，而 `(Equiv-Reflection)` 正是用于填补这个空缺，强制所有相等性都可被内化为真。

---
###### 引理 4.3.3.3 ((Equiv-elim)的独立性)

**模型 `M_broken_elim`**

这个模型的目标是使 `(Equiv-Elim)` 失效，同时保持 `(Reif)` 和 `(Equiv-Reflection)` 有效。

核心思想是设计一个 `equiv` 的解释，使得它在某些参数**不相等**的情况下，也能返回代表“真”的值。这将成为我们打破 `(Equiv-Elim)` 的突破口。同时，这个解释必须足够精巧，以满足 `(Reif)` 苛刻的自反具体化要求。

**1. 模型定义**

*   **域 (Domain):** 我们使用一个包含三个元素的三值逻辑域：
    $D = \{ \mathbf{T}, \mathbf{F}, \mathbf{U} \}$
    其中：
    *   $\mathbf{T}$ 代表 “真” (Truth)
    *   $\mathbf{F}$ 代表 “假” (Falsehood)
    *   $\mathbf{U}$ 代表 “不确定的” 或 “数据” (Undefined/Data)

*   **解释函数 (Interpretation)** $〚·〛$:
    1.  $〚()〛 := \mathbf{T}$
    2.  $〚\text{pair}(...)〛 := \mathbf{U}$
    3.  $〚\text{false\_const}〛 := \mathbf{F}$ (假设签名中有一个用于我们反例的常量)
    4.  $〚\text{其他数据构造}〛 := \mathbf{U}$
    5.  $〚[t_1 \equiv t_2]〛$ 的解释由一个函数 $f_{equiv}: D \times D \to D$ 给出，其定义如下：
        $$
        f_{equiv}(a, b) :=
        \begin{cases}
        \mathbf{T} & \text{if } a = b \\
        \mathbf{T} & \text{if } \{a, b\} = \{\mathbf{F}, \mathbf{U}\} \quad \text{-- 这是特意设计的漏洞} \\
        \mathbf{F} & \text{if } \{a, b\} = \{\mathbf{T}, \mathbf{F}\} \\
        \mathbf{U} & \text{if } \{a, b\} = \{\mathbf{T}, \mathbf{U}\} \\
        \end{cases}
        $$
        (注意：由于 `equiv` 是可交换的，我们使用集合 `{a,b}` 来定义，这覆盖了 `(a,b)` 和 `(b,a)` 两种情况。)

**2. 规则有效性验证**

**(Reif) 有效**
我们需要证明 `〚t〛 = 〚[t ≡ ()]〛` 对任意项 `t` 成立。设 `v = 〚t〛`，这等价于证明 `v = f_{equiv}(v, 〚()〛) = f_{equiv}(v, \mathbf{T})` 对所有 `v \in D` 成立。

*   **情形 1: `v = T`**
    *   LHS = $\mathbf{T}$
    *   RHS = $f_{equiv}(\mathbf{T}, \mathbf{T})$。根据 $f_{equiv}$ 定义的第一条规则 (`a=b`)，结果为 $\mathbf{T}$。
    *   $\mathbf{T} = \mathbf{T}$，成立。

*   **情形 2: `v = F`**
    *   LHS = $\mathbf{F}$
    *   RHS = $f_{equiv}(\mathbf{F}, \mathbf{T})$。根据 $f_{equiv}$ 定义的第三条规则 (`{a,b} = {T, F}`)，结果为 $\mathbf{F}$。
    *   $\mathbf{F} = \mathbf{F}$，成立。

*   **情形 3: `v = U`**
    *   LHS = $\mathbf{U}$
    *   RHS = $f_{equiv}(\mathbf{U}, \mathbf{T})$。根据 $f_{equiv}$ 定义的第四条规则 (`{a,b} = {T, U}`)，结果为 $\mathbf{U}$。
    *   $\mathbf{U} = \mathbf{U}$，成立。

由于所有情况都成立，`(Reif)` 在此模型中是有效的。

**(Equiv-Reflection) 有效**
我们需要证明：若 `〚t₁〛 = 〚t₂〛`，则 `〚[t₁ ≡ t₂]〛 = 〚()〛`。设 `v = 〚t₁〛 = 〚t₂〛`，这等价于证明 `f_{equiv}(v, v) = \mathbf{T}`。

*   根据 $f_{equiv}$ 定义的第一条规则，当两个参数相等时 (`a=b`)，函数总是返回 $\mathbf{T}$。
*   因此，`(Equiv-Reflection)` 在此模型中是有效的。

**(Equiv-Elim) 失效**
我们需要构造一个反例，即找到两个项 `t₁` 和 `t₂`，使得 `〚[t₁ ≡ t₂]〛 = 〚()〛` 成立，但 `〚t₁〛 ≠ 〚t₂〛`。

*   **选择反例项**:
    *   令 `t₁ := false_const`
    *   令 `t₂ := pair()`

*   **验证其解释**:
    *   `〚t₁〛 = 〚false_const〛 = \mathbf{F}`
    *   `〚t₂〛 = 〚pair()〛 = \mathbf{U}`
    *   显然，`〚t₁〛 ≠ 〚t₂〛`。

*   **验证前提**: 我们需要检查 `〚[t₁ ≡ t₂]〛 = 〚()〛` 是否成立。
    *   LHS = `〚[false_const ≡ pair()]〛 = f_{equiv}(\mathbf{F}, \mathbf{U})`。
    *   根据 $f_{equiv}$ 定义的第二条规则（我们特意设计的漏洞），当 `{a, b} = \{\mathbf{F}, \mathbf{U}\}$ 时，结果为 $\mathbf{T}$。
    *   RHS = `〚()〛 = \mathbf{T}`。
    *   由于 LHS = RHS = $\mathbf{T}$，前提成立。

*   **结论**:
    我们找到了一个情况，其中规则的前提 (`(false_const ≡ pair()) ~ ()`) 在模型中成立，但其结论 (`false_const ~ pair()`) 在模型中不成立。
    因此，`(Equiv-Elim)` 规则在此模型中是**无效的**。

---
**总结**
我们成功构造了模型 `M_broken_elim`。通过精心设计三值域上的 `equiv` 解释函数，我们使其：
1.  **满足 (Reif)**：通过确保 `f_equiv(v, T)` 的结果总是 `v`。
2.  **满足 (Equiv-Reflection)**：通过确保 `f_equiv(v, v)` 的结果总是 `T`。
3.  **打破 (Equiv-Elim)**：通过引入一个特例 `f_equiv(F, U) = T`，它使得一个 `equiv` 项可以为真，即使其参数不相等。

---
##### **4.3.4. 定理：内化等价操作符 `≡` 的代数性质**

本节将分析核心操作符 `≡` 在 `CIE` 证明论体系下的两个基本代数性质：交换律和结合律。我们将证明 `≡` 是可证交换的，但并非结合的。

---
**引理 4.3.4.1 (`≡` 的可证交换律)**
操作符 `≡` 满足交换律。即，对于任意上下文 `Γ` 和任意项 `t₁, t₂`，以下判断是可证的：
$$ \Gamma \vdash [t_1 \equiv t_2] \sim [t_2 \equiv t_1] $$

**证明.**
此证明是规则 `(Equiv-Intro)` 和 `(Sym)` 的直接推论。规则 `(Equiv-Intro)` 允许我们当两个判断 `A` 和 `B` 可互推时，证明其内化表示等价。

为证明 `Γ ⊢ [t₁ ≡ t₂] ~ [t₂ ≡ t₁]`，我们令 `A := (t₁ ~ t₂)` 且 `B := (t₂ ~ t₁)`，并证明 `(Equiv-Intro)` 的两个前提：

1.  **证明前提 1: `Γ, t₁ ~ t₂ ⊢ t₂ ~ t₁`**
    $$ \dfrac{\dfrac{}{\Gamma, t_1 \sim t_2 \vdash t_1 \sim t_2} \text{ (Hypothesis)}}{\Gamma, t_1 \sim t_2 \vdash t_2 \sim t_1} \text{ (Sym)} $$
    在 `t₁ ~ t₂` 的假设下，应用对称性规则 `(Sym)` 即可得证。

2.  **证明前提 2: `Γ, t₂ ~ t₁ ⊢ t₁ ~ t₂`**
    $$ \dfrac{\dfrac{}{\Gamma, t_2 \sim t_1 \vdash t_2 \sim t_1} \text{ (Hypothesis)}}{\Gamma, t_2 \sim t_1 \vdash t_1 \sim t_2} \text{ (Sym)} $$
    同理，在 `t₂ ~ t₁` 的假设下，应用 `(Sym)` 即可得证。

由于 `(Equiv-Intro)` 的两个前提均可证，我们可以得出结论：`Γ vdash; [t₁ ≡ t₂] ~ [t₂ ≡ t₁]`。这表明 `≡` 的交换性是 `~` 关系对称性的一个内化结果。
**Q.E.D.**

---
**引理 4.3.4.2 (`≡` 的不可证结合律)**
操作符 `≡` 不满足结合律。即，以下结合律公式在 `CIE` 中**不是**一个普遍可证的定理模式：
$$ \Gamma \vdash [[a \equiv b] \equiv c] \sim [a \equiv [b \equiv c]] $$

**证明.**
`≡` 的结合律在语义上是不直观的。左侧 `[[a ≡ b] ≡ c]` 比较的是一个**命题**（`a ≡ b`）与一个**项**（`c`）的等价性，而右侧 `[a ≡ [b ≡ c]]` 比较的是一个**项**（`a`）与一个**命题**（`b ≡ c`）的等价性。`CIE` 的规则并未提供对此类结构进行重组的通用机制。

我们将通过构造一个反例模型来严格证明这一点。我们复用 **引理 4.3.3.1** 中用于证明 `(Reif)` 独立性的三值模型 `M₁`：
*   **域 (Domain):** $D = \{\top, \bot, \delta\}$
*   **解释函数 (Interpretation)** $〚·〛_{M₁}$:
    *   $〚()〛 := \top$
    *   $〚\text{pair}(...)〛 := \delta$ (以及其他任何非 `equiv` 的数据构造)
    *   $〚[t_1 \equiv t_2]〛 := \top$ 若 $〚t_1〛 = 〚t_2〛$，否则为 $\bot$。

现在，我们选择以下项作为反例：
*   `a := pair()`
*   `b := pair()`
*   `c := ()`

它们的语义解释为 $〚a〛 = \delta$, $〚b〛 = \delta$, $〚c〛 = \top$。我们计算结合律公式两边的解释值：

1.  **左侧 (LHS):** $〚[[a \equiv b] \equiv c]〛$
    *   内层: $〚a \equiv b〛$。由于 $〚a〛 = \delta = 〚b〛$，其值为 `⊤`。
    *   外层: $〚\top \equiv c〛$。由于 $〚c〛 = \top$，其值为 `⊤`。
    *   因此, **LHS = `⊤`**。

2.  **右侧 (RHS):** $〚[a \equiv [b \equiv c]]〛$
    *   内层: $〚b \equiv c〛$。由于 $〚b〛 = \delta \neq \top = 〚c〛$，其值为 `⊥`。
    *   外层: $〚a \equiv \bot〛$。由于 $〚a〛 = \delta \neq \bot$，其值为 `⊥`。
    *   因此, **RHS = `⊥`**。

由于 `LHS (⊤) ≠ RHS (⊥)`，结合律在此模型中不成立。根据系统的可靠性定理（5.2.2），任何可证的判断必须在所有可靠模型中都有效。因此，结合律在 `CIE` 中是不可证的。
**Q.E.D.**

##### **4.3.5. 保守性 (Conservativity)**

本节的目标是证明 CIE 是其代数子系统 `CIE⁻` 的一个**保守扩展**。即，任何仅使用代数符号可表达的、能在完整 CIE 系统中证明的等价关系，也必然能在纯代数子系统中证明。这一性质至关重要，因为它保证了系统的逻辑部分（与 `equiv` 相关的规则）不会“污染”纯代数推理，确保了系统的模块化和可预测性。

###### **4.3.5.1. 形式化定义**

1.  **代数签名**: $\Sigma^- = \Sigma \setminus \{\text{equiv}\}$。
2.  **代数项**: $T_{\Sigma^-}(V)$，即不含 `equiv` 符号的项。
3.  **代数上下文**: $\Gamma^-$，一个所有判断 `l~r` 都满足 $l, r \in T_{\Sigma^-}(V)$ 的上下文。
4.  **代数子系统 `CIE⁻`**: 由以下规则构成的系统，其所有判断都基于代数项和代数上下文：
    *   **(A) 结构规则**: (Refl), (Sym), (Trans)。
    *   **(B) 同余规则**: (Cong)，其中函数符号 $f \in \Sigma^-$。
    *   **(C) 假设规则**: (Hyp-Schema) 和 (Hyp-Local)，其中上下文为 $\Gamma^-$。

###### **4.3.5.2. 保守性定理**

**定理 4.3.5.2 (保守性)**
对于任意代数上下文 $\Gamma^-$ 和任意代数项 $t_1, t_2 \in T_{\Sigma^-}(V)$，
$$ \text{若 } \Gamma^- \vdash_{\text{CIE}} t_1 \sim t_2 \text{ 可证，则 } \Gamma^- \vdash_{\text{CIE}^-} t_1 \sim t_2 \text{ 亦可证。} $$

---
###### **4.3.5.3. 证明**

我们将通过一个语义学论证来证明此定理。其核心思想是表明，任何 `CIE⁻` 的代数模型都可以被“无害地”扩展为一个 `CIE` 模型，且该扩展在所有代数项上的解释与原模型一致。

**第一步：`CIE⁻` 的模型论**

一个 **`CIE⁻`-代数模型** `A` 由一个非空集合 `D` (域) 和一个解释函数 `〚·〛_A` 构成，该函数将 $\Sigma^-$ 中的每个 $n$-元函数符号 $f$ 映射为 `D` 上的一个函数 $f_A: D^n \to D$。对于一个估值 $\nu: V \to D$，解释函数可以唯一地扩展为对所有代数项 $t \in T_{\Sigma^-}(V)$ 的同态 `〚t〛_{A,ν}`。

我们说模型 `A` 满足上下文 $\Gamma^-$，记为 $A \models \Gamma^-$，当且仅当对于 `Γ⁻` 中的每个判断 `l~r` 和所有估值 `ν`，都有 `〚l〛_{A,ν} = 〚r〛_{A,ν}`。根据 `CIE⁻` (一个标准的等式逻辑系统) 的声音性和完备性，$\Gamma^- \vdash_{\text{CIE}^-} t_1 \sim t_2$ 成立当且仅当对于所有满足 $\Gamma^-$ 的 `CIE⁻`-模型 `A`，都有 $A \models t_1 \sim t_2$。

**第二步：模型扩展**

设 `A` 是任意一个满足 $\Gamma^-$ 的 `CIE⁻`-模型，其域为 `D`。我们构造一个 **`CIE`-模型 `A'`** 如下：
1.  **域**: `A'` 的域与 `A` 相同，即 `D`。
2.  **代数符号的解释**: 对于所有 $f \in \Sigma^-$，`A'` 中 `f` 的解释与 `A` 中 `f` 的解释相同。
3.  **逻辑符号的解释**:
    *   选择 `D` 中两个元素 `d_true` 和 `d_false`。（若 `D` 只有一个元素，则令 `d_true = d_false`；否则选择两个不同的元素。）
    *   定义 `〚unit〛_{A'} := d_true`。
    *   定义 `〚equiv(t₁, t₂)〛_{A',ν} :=`
        *   `d_true`，如果 `〚t₁〛_{A',ν} = 〚t₂〛_{A',ν}`
        *   `d_false`，如果 `〚t₁〛_{A',ν} ≠ 〚t₂〛_{A',ν}`

通过直接检查，可以验证 `A'` 满足 `CIE` 的所有推理规则，因此 `A'` 是一个有效的 `CIE` 模型。例如，对于 `(Equiv-Elim)` 规则，若 `〚(t₁ ≡ t₂)〛_{A',ν} = 〚()〛_{A',ν}`，则意味着 `〚(t₁ ≡ t₂)〛_{A',ν} = d_true`，根据 `equiv` 的解释，这当且仅当 `〚t₁〛_{A',ν} = 〚t₂〛_{A',ν}`，故规则成立。其他逻辑规则的可靠性也可以类似地验证。

**第三步：论证**

1.  假设 $\Gamma^- \vdash_{\text{CIE}} t_1 \sim t_2$，其中 $t_1, t_2 \in T_{\Sigma^-}(V)$。
2.  根据 `CIE` 的可靠性（定理 5.2.2），这意味着对于任何满足 `Γ⁻` 的 `CIE` 模型 `M` 和任何估值 `ν`，都有 `〚t₁〛_{M,ν} = 〚t₂〛_{M,ν}`。
3.  现在，考虑在第一步中定义的任意一个满足 $\Gamma^-$ 的 `CIE⁻`-模型 `A`。
4.  根据第二步的构造，我们可以从 `A` 构建一个 `CIE` 模型 `A'`。由于 `A'` 对代数符号的解释与 `A` 相同，`A'` 显然也满足代数上下文 `Γ^-`。
5.  因为 `A'` 是一个满足 `Γ⁻` 的 `CIE` 模型，根据第 2 点，结论 `〚t₁〛_{A',ν} = 〚t₂〛_{A',ν}` 必须在 `A'` 中成立。
6.  根据构造，`A'` 和 `A` 对所有代数项的解释是完全相同的。因此，`〚t₁〛_{A,ν} = 〚t₁〛_{A',ν}` 且 `〚t₂〛_{A,ν} = 〚t₂〛_{A',ν}`。
7.  结合 5 和 6，我们得出 `〚t₁〛_{A,ν} = 〚t₂〛_{A,ν}`。
8.  由于 `A` 是一个**任意**满足 `Γ⁻` 的 `CIE⁻`-模型，我们已经证明 `t₁ ~ t₂` 在所有这样的模型中都有效。
9.  根据 `CIE⁻` 的完备性，这等价于 $\Gamma^- \vdash_{\text{CIE}^-} t_1 \sim t_2$。

**结论**

我们已经证明，任何在 `CIE` 中可证的纯代数判断，在 `CIE⁻` 中也必定可证。因此，CIE 是其代数子系统 `CIE⁻` 的一个保守扩展。

**Q.E.D.**

---
##### **4.3.6. 定理：证明论等价关系的结构二分性 (Structural Dichotomy of the Proof-Theoretic Equivalence)**

本节旨在对 `CIE` 证明论体系在空上下文 `Γ=∅` 下所引致的等价关系 `~` 进行精确的结构性刻画。我们将严格证明，项的宇宙被 `~` 关系划分为两种截然不同的形态：一个单一的、包含所有可证等价于真值 `()` 的项的“真理”等价类；以及无数个其他等价类，其中任意两个**非逻辑项（non-logical terms）** 之间的等价性完全由一个更受限的、纯粹结构性的再化规则集所生成。

---
**定义 4.3.6.1 (真值可证项)**
一个项 `t` 被称为**真值可证的 (Truth-Provable)**，当且仅当 `∅ ⊢ t ~ ()` 在 CIE 中是可证的。

---
**定理 4.3.6.2 (真理等价类的坍缩)**
所有真值可证的项构成一个单一的等价类。即，若 `t` 和 `s` 均为真值可证的项，则 `∅ ⊢ t ~ s`。

**证明.**
根据定义，我们有前提 `∅ ⊢ t ~ ()` 和 `∅ ⊢ s ~ ()`。
1.  由 `∅ ⊢ s ~ ()` 和规则 **(Sym)**，可得 `∅ ⊢ () ~ s`。
2.  由 `∅ ⊢ t ~ ()` 和 `∅ ⊢ () ~ s`，应用规则 **(Trans)**，可得 `∅ ⊢ t ~ s`。
**Q.E.D.**

---
**定义 4.3.6.3 (再化子系统 CIE_R)**
`CIE_R` 是一个仅包含以下推理规则的子系统，其可证性关系记为 `⊢_R`：
*   **(Refl)**, **(Sym)**, **(Trans)**
*   **(Cong)**
*   **(Reif)**
`CIE_R` 系统在句法上排除了所有显式依赖于 `()` 作为特殊真值的规则，即 `(Equiv-Elim)` 和 `(Equiv-Reflection)`，以及引入假设的 `(Equiv-Intro)`。

---
**引理 4.3.6.4 (分离引理)**
若 `t` 不是一个真值可证项，而 `s` 是一个真值可证项，则 `∅ ⊢ t ~ s` 不可证。

**证明.**
我们使用第 5.1 节中为证明一致性而构造的语义模型 `M`，其域为 `D = {1, 0}`。
1.  若 `s` 是一个真值可证项，则 `∅ ⊢ s ~ ()`。根据 `CIE` 相对于模型 `M` 的可靠性，必有 `∅ ⊨ s ~ ()`，这意味着对任意估值 `ν`，`〚s〛_ν = 〚()〛_ν = 1`。
2.  若 `t` 不是一个真值可证项，则 `∅ ⊬ t ~ ()`。根据可靠性，`∅ \not\models t \sim ()`，这意味着存在某个估值 `ν₀` 使得 `〚t〛_{ν₀} ≠ 〚()〛_{ν₀} = 1`。因此，必然存在 `ν₀` 使得 `〚t〛_{ν₀} = 0`。
3.  现在，采用反证法。假设 `∅ ⊢ t ~ s` 可证。根据可靠性，必有 `∅ ⊨ t ~ s`，即对**所有**估值 `ν`，`〚t〛_ν = 〚s〛_ν`。
4.  结合 (1) 和 (3)，我们得到对所有 `ν`，`〚t〛_ν = 1`。但这与 (2) 中（存在一个 `ν₀` 使 `〚t〛_{ν₀} = 0`）的结论相矛盾。
因此，初始假设 `∅ ⊢ t ~ s` 可证是错误的。
**Q.E.D.**

---
**定义 4.3.6.5 (推导的尺寸)**
一个推导 `D` 的**尺寸**，记为 `size(D)`，定义为推导树中推理规则的应用总次数。

---
**定义 4.3.6.6 (非逻辑项)**
一个项 `t` 被称为**非逻辑项 (Non-logical Term)**，当且仅当其顶层函数符号不为 `equiv`。

---
**定理 4.3.6.7 (非真值等价类的结构 - 修订版)**
若 `t` 和 `s` 均为**非逻辑项**且均**不是**真值可证项，则 `∅ ⊢ t ~ s` 在 CIE 中可证，当且仅当 `∅ ⊢_R t ~ s` 在再化子系统 `CIE_R` 中可证。

**证明.**

($\Leftarrow$) **方向 (CIE_R ⊂ CIE)**:
由于 `CIE_R` 的所有推理规则都是 `CIE` 的规则子集，任何在 `CIE_R` 中的有效证明都直接是一个有效的 `CIE` 证明。

($\Rightarrow$) **方向 (CIE ⊂ CIE_R for non-Truth-Provable, Non-logical Terms)**:
我们采用**反证法**。假设存在一个或多个 `CIE` 推导，其结论为 `∅ ⊢ t ~ s`，其中 `t` 和 `s` 满足定理的前提（非逻辑项、非真值可证），但该结论在 `CIE_R` 中不可证。根据良序原则，令 `D_min` 是所有这类推导中**尺寸最小**的一个，其结论为 `∅ ⊢ t_0 ~ s_0`。

我们对 `D_min` 的最后一条推理规则进行穷尽式案例分析。

*   **案例 1: 句法不匹配的规则**
    *   **(Equiv-Intro)**: 此规则的结论形式为 `(t₁ ≡ t₂) ~ (s₁ ≡ s₂)`。其结论中的项 `(t₁ ≡ t₂)` 和 `(s₁ ≡ s₂)` 的顶层构造子均为 `equiv`。这与定理前提——`t_0` 和 `s_0` 均为**非逻辑项**——直接矛盾。因此，`D_min` 的最后一步不可能是 `(Equiv-Intro)`。
    *   **(Equiv-Reflection)**: 结论形式为 `(a ≡ b) ~ ()`。由于 `s_0` 不是真值可证项，根据**分离引理 4.3.6.4**，它不能被证明等价于 `()`。此规则不适用。
    *   **(Hyp-*)**: 上下文为空，不适用。

*   **案例 2: 属于 `CIE_R` 的规则**
    *   若最后规则是 `(Refl)` 或 `(Reif)`，其结论可直接在 `CIE_R` 中推导，与 `D_min` 的假设（在 `CIE_R` 中不可证）矛盾。
    *   若最后规则是 `(Sym)`、`(Trans)` 或 `(Cong)`。以 `(Trans)` 为例，其前提为 `∅ ⊢ t_0 ~ u` 和 `∅ ⊢ u ~ s_0`。
        1.  根据**分离引理 4.3.6.4**，由于 `t_0` 和 `s_0` 都不是真值可证项，中间项 `u` 也必须不是真值可证项。此外，对前提推导 `D₁` 和 `D₂` 的结构进行简单归纳可知，若 `t_0` 和 `s_0` 为非逻辑项，`u` 也必须为非逻辑项。
        2.  这两个前提的推导 `D₁` 和 `D₂` 的尺寸都严格小于 `size(D_min)`。
        3.  根据 `D_min` 的最小性，`D₁` 和 `D₂` 的结论必然在 `CIE_R` 中是可证的（因为它们满足定理的所有前提且其推导尺寸更小）。
        4.  由于 `(Trans)` 也是 `CIE_R` 的规则，我们可以用这两个 `CIE_R` 证明构造一个 `∅ ⊢_R t_0 ~ s_0` 的 `CIE_R` 证明。
        5.  这与 `D_min` 的假设矛盾。
    *   因此，`D_min` 的最后一条规则不能属于 `CIE_R`。

*   **案例 3: 核心逻辑规则 `(Equiv-Elim)`**
    *   若最后一步是此规则，则结论 `∅ ⊢ t_0 ~ s_0` 来自前提 `∅ ⊢ (t_0 ≡ s_0) ~ ()`。
        1.  这个前提的推导，记为 `D₁`，其尺寸 `size(D₁) < size(D_min)`。
        2.  `D₁` 的结论表明，项 `(t_0 ≡ s_0)` 是一个**真值可证项**。
        3.  对推导 `D₁` 的结构进行分析，可以发现，任何非平凡的真值可证判断的推导，其“创造”出与 `()` 的等价性的源头必然是 `(Equiv-Reflection)` 或 `(Equiv-Elim)`。在一个最小推导链中，最终必然依赖于 `(Equiv-Reflection)`。
        4.  这意味着在 `D₁` 的推导树中，必然存在一个 `(Equiv-Reflection)` 的应用，其前提是：`∅ ⊢ t_0 ~ s_0`。
        5.  这个前提由一个推导 `D₂` 证明，其中 `size(D₂) < size(D₁) < size(D_min)`。
        6.  我们从一个假定的**最小**反例推导 `D_min`（结论 `∅ ⊢ t_0 ~ s_0`）出发，推导出必须存在一个尺寸**严格更小**的推导 `D₂`，它证明了**完全相同的结论**。这与 `D_min` 的最小性相矛盾。

**结论**
所有可能的情况都导向了矛盾。因此，我们最初的假设——存在一个满足定理前提但在 `CIE_R` 中不可证的 `CIE` 推导——是错误的。

**Q.E.D.**

---

### **5. CIE 一致性的证明**

#### 5.1. 模型论证明

我们将通过构造一个语义模型 `M` 并证明 `CIE` 的所有推理规则在该模型下都是可靠的（Sound）来完成此任务。然后，我们将展示一个特定的、我们不希望其为真的判断（例如 `⟨⟩ ~ ()`）在该模型中为假，从而根据可靠性定理得出该判断在 `CIE` 中是不可证的。

##### **5.1.1 模型 `M` 的定义**

我们的模型将使用最简单的非平凡域：布尔代数。

*   **域 (Domain)**:
    $D = \{1, 0\}$，其中 `1` 代表“真”或“已定义”，`0` 代表“假”或“数据”。

*   **估值 (Valuation)**:
    一个估值 $\nu$ 是一个从变量集合 $V$ 到域 $D$ 的函数，即 $\nu: V \to D$。

*   **解释函数 (Interpretation)**:
    解释函数 $〚t〛_\nu$ 将一个项 $t$ 和一个估值 $\nu$ 映射到域 $D$ 中的一个值。
    1.  $〚x〛_\nu := \nu(x)$  (对于变量 $x \in V$)
    2.  $〚()〛_\nu := 1$
    3.  $〚\text{pair}(t_1, t_2)〛_\nu := 0$
    4.  $〚f(t_1, \dots, t_n)〛_\nu := 0$  (对于任何用户定义的 $f \in \Sigma$)
    5.  $〚[t_1 \equiv t_2]〛_\nu := \begin{cases} 1 & \text{若 } 〚t_1〛_\nu = 〚t_2〛_\nu \\ 0 & \text{否则} \end{cases}$

    这个解释的关键在于：`()` 是唯一的“真”值。所有数据结构，如 `pair` 或用户定义的构造，都被映射到 `0`。内化的等价 `[t₁ ≡ t₂]` 则被解释为对其参数解释值的元语言等价性测试。

*   **语义满足与后承 (Semantic Satisfaction and Entailment)**:
    *   一个估值 $\nu$ **满足**一个判断 $t_1 \sim t_2$，记作 $\nu \models t_1 \sim t_2$，当且仅当 $〚t_1〛_\nu = 〚t_2〛_\nu$。
    *   一个估值 $\nu$ **满足**一个上下文 $\Gamma$，记作 $\nu \models \Gamma$，当且仅当对于 $\Gamma$ 中的每一个判断 $(l, r)$ 都满足以下相应条件：
        1.  若 $vars(l) ∪ vars(r) = ∅$ (局部公理), 则 $〚l〛_ν = 〚r〛_ν$。
        2.  若 $vars(l) ∪ vars(r) ≠ ∅$ (公理模式), 则对于**所有**估值 $μ: V → D$，都有 $〚l〛_μ = 〚r〛_μ$。
    *   一个上下文 $\Gamma$ **语义上蕴含**一个判断 $t_1 \sim t_2$，记作 $\Gamma \models t_1 \sim t_2$，当且仅当对于**所有**估值 $\nu$，如果 $\nu \models \Gamma$，那么 $\nu \models t_1 \sim t_2$。

    *   **形式化注记**: 请注意公理模式的语义满足条件的定义（第2条）包含一个**对所有估值的全称量化**。这是一个非标准的、但对于本系统至关重要的定义。它要求上下文中的公理模式必须在模型中是有效公式（重言式）。这一强条件是确保 $(Hyp-Schema)$ 规则（该规则允许对假设进行任意替换）的语义可靠性的关键。在形式化时必须精确实现此定义，否则一致性证明将失败。

##### **5.1.2. 可靠性定理 (Soundness Theorem)**

**引理 5.1.2.1 (语义替换引理)**
对于模型 `M`，任意替换 $\theta: V \to T_\Sigma(V)$，任意估值 $\nu: V \to D$，以及任意项 $t \in T_\Sigma(V)$，以下等式成立：
$$ 〚\theta(t)〛_\nu = 〚t〛_{\nu'} $$
其中新估值 $\nu': V \to D$ 定义为 $\nu'(x) := 〚\theta(x)〛_\nu$ 对所有 $x \in V$。

**证明**:
我们对项 `t` 的结构进行归纳。
*   **基础情形 (t 是变量 x)**:
    $〚\theta(x)〛_\nu = 〚x〛_{\nu'} = \nu'(x)$。根据 $\nu'$ 的定义，$\nu'(x) = 〚\theta(x)〛_\nu$。等式成立。
*   **归纳步骤 (t 是复合项 f(t₁,...,tₙ))**:
    假设引理对 $t_1, \dots, t_n$ 成立 (归纳假设)。我们需要证明 $〚\theta(f(t_1,\dots,t_n))〛_\nu = 〚f(t_1,\dots,t_n)〛_{\nu'}$。
    *   $〚\theta(f(t_1,\dots,t_n))〛_\nu = 〚f(\theta(t_1),\dots,\theta(t_n))〛_\nu$。
    *   我们对函数符号 `f` 进行分类讨论，应用解释函数 `〚·〛` 的定义：
        *   若 `f` 是 `pair` 或用户定义的函数，则 $〚f(\dots)〛_\nu$ 和 $〚f(\dots)〛_{\nu'}$ 均被解释为 `0`，二者相等。
        *   若 `f` 是 `equiv` (即 $t=[t_1 \equiv t_2]$)，则：
            $〚\theta([t_1 \equiv t_2])〛_\nu = 〚[\theta(t_1) \equiv \theta(t_2)]〛_\nu$
            $= (1 \text{ if } 〚\theta(t_1)〛_\nu = 〚\theta(t_2)〛_\nu \text{ else } 0)$
            根据归纳假设，这等价于
            $= (1 \text{ if } 〚t_1〛_{\nu'} = 〚t_2〛_{\nu'} \text{ else } 0)$
            $= 〚[t_1 \equiv t_2]〛_{\nu'}$。
    *   在所有情况下，等式均成立。引理得证。
**Q.E.D.**

**定理 5.1.2.2 (可靠性定理)**: 如果一个相继 $\Gamma \vdash t_1 \sim t_2$ 在 `CIE` 中是可证的，那么它在模型 `M` 中是有效的，即 $\Gamma \models t_1 \sim t_2$。

**证明**:
我们对 `Γ ⊢ t₁ ~ t₂` 的推导结构进行归纳。我们需要证明 `CIE` 的每一个推理规则都是保真（truth-preserving）的，即如果其前提在语义上有效，其结论也必然在语义上有效。

*   **A. 结构规则 (Structural Rules)**
    *   **(Refl)**: $\overline{\Gamma \vdash t \sim t}$。我们需要证明 $\Gamma \models t \sim t$。对于任何满足 $\Gamma$ 的 $\nu$，根据等式的自反性，必然有 $〚t〛_\nu = 〚t〛_\nu$。成立。
    *   **(Sym)** & **(Trans)**: 类似地，这两个规则的可靠性直接来自于等式关系的对称性和传递性。

*   **B. 同余规则 (Congruence Rule)**
    *   **(Cong)**: 假设前提 $\Gamma \models t_i \sim s_i$ 对所有 $i=1,\dots,n$ 成立。我们需要证明 $\Gamma \models f(t_1,\dots,t_n) \sim f(s_1,\dots,s_n)$。
        *   令 $\nu$ 为任何满足 $\Gamma$ 的估值。根据归纳假设， $〚t_i〛_\nu = 〚s_i〛_\nu$ 对所有 $i$ 成立。
        *   如果 $f$ 是 `pair` 或用户定义的函数，则 $〚f(t_1,\dots)〛_\nu = 0$ 且 $〚f(s_1,\dots)〛_\nu = 0$。二者相等。
        *   如果 $f$ 是 `equiv`，我们需要证明 $〚[t_1 \equiv t_2]〛_\nu = 〚[s_1 \equiv s_2]〛_\nu$。根据归纳假设 $〚t_1〛_\nu = 〚s_1〛_\nu$ 和 $〚t_2〛_\nu = 〚s_2〛_\nu$。因此，元语言判断 `(〚t₁〛_ν = 〚t₂〛_ν)` 与 `(〚s₁〛_ν = 〚s₂〛_ν)` 逻辑等价。所以它们的解释（`1` 或 `0`）必然相同。
        *   在所有情况下，结论都成立。

*   **C. 假设规则 (Hypothesis Rules)**
    *   **(Hyp-Local)**: 假设 `(l ~ r) ∈ Γ` 是一个**局部公理**。我们需要证明 `Γ ⊨ l ~ r`。根据定义，任何满足 `Γ` 的估值 `ν` 必须满足 `l ~ r`，即 `〚l〛_ν = 〚r〛_ν`。成立。
    *   **(Hyp-Schema)**: 假设 `(l ~ r) ∈ Γ` 是一个**公理模式**。我们需要证明 `Γ ⊨ θ(l) ~ θ(r)`。
        1.  令 `ν` 为任何满足 `Γ` 的估值。我们的目标是证明 `〚θ(l)〛_ν = 〚θ(r)〛_ν`。
        2.  根据公理模式的语义定义(2.1.1)，`(l ~ r) ∈ Γ` 意味着它对**任何**估值都成立。
        3.  我们构造一个新的估值 `ν': V → D`，定义为 `ν'(x) := 〚θ(x)〛_ν` 对所有 $x \in V$。
        4.  由于 `l ~ r` 对所有估值都成立，它对 `ν'` 也成立。因此 `〚l〛_{ν'} = 〚r〛_{ν'}`。
        5.  根据刚刚证明的 **引理 5.2.1 (语义替换引理)**，我们有 `〚θ(l)〛_ν = 〚l〛_{ν'}` 和 `〚θ(r)〛_ν = 〚r〛_{ν'}`。
        6.  结合以上两点，我们得到 `〚θ(l)〛_ν = 〚l〛_{ν'} = 〚r〛_{ν'} = 〚θ(r)〛_ν`。结论成立。

*   **D. 等价内化规则 (Equivalence Internalization Rules)**
    *   **(Equiv-Reflection)**: 假设 $\Gamma \models t_1 \sim t_2$。我们需要证明 $\Gamma \models [t_1 \equiv t_2] \sim ()$。
        *   令 $\nu$ 为任何满足 $\Gamma$ 的估值。根据前提，$〚t_1〛_\nu = 〚t_2〛_\nu$。
        *   根据 `≡` 的解释，$〚[t_1 \equiv t_2]〛_\nu$ 此时为 `1`。而 $〚()〛_\nu$ 恒为 `1`。因此二者相等。
    *   **(Equiv-Elim)**: 假设 $\Gamma \models [t_1 \equiv t_2] \sim ()$。我们需要证明 $\Gamma \models t_1 \sim t_2$。
        *   令 $\nu$ 为任何满足 $\Gamma$ 的估值。根据前提，$〚[t_1 \equiv t_2]〛_\nu = 〚()〛_\nu = 1$。
        *   根据 `≡` 的解释，$〚[t_1 \equiv t_2]〛_\nu$ 为 `1` 的唯一条件是 $〚t_1〛_\nu = 〚t_2〛_\nu$。这正是结论。
    *   **(Equiv-Intro)**: 假设
        1.  $\Gamma \cup \{t_1 \sim t_2\} \models s_1 \sim s_2$
        2.  $\Gamma \cup \{s_1 \sim s_2\} \models t_1 \sim t_2$
        我们需要证明 $\Gamma \models [t_1 \equiv t_2] \sim [s_1 \equiv s_2]$。
        *   令 $\nu$ 为任何满足 $\Gamma$ 的估值。我们需要证明 $〚[t_1 \equiv t_2]〛_\nu = 〚[s_1 \equiv s_2]〛_\nu$。这等价于证明布尔表达式 `(〚t₁〛_ν = 〚t₂〛_ν)` 和 `(〚s₁〛_ν = 〚s₂〛_ν)` 是等价的。
        *   **情况 1**: 假设 `〚t₁〛_ν = 〚t₂〛_ν`。这意味着 `ν` 满足 `t₁ ~ t₂`。由于 `ν` 也满足 `Γ`，所以 `ν` 满足 `Γ ∪ {t₁ ~ t₂}`。根据前提1，`ν` 必须满足 `s₁ ~ s₂`，即 `〚s₁〛_ν = 〚s₂〛_ν`。
        *   **情况 2**: 假设 `〚s₁〛_ν = 〚s₂〛_ν`。同理，根据前提2，`ν` 必须满足 `t₁ ~ t₂`，即 `〚t₁〛_ν = 〚t₂〛_ν`。
        *   综合两种情况，我们证明了 `(〚t₁〛_ν = 〚t₂〛_ν) ⇔ (〚s₁〛_ν = 〚s₂〛_ν)`。因此它们的解释值（`1` 或 `0`）必然相同。
	*   **形式化注记:** 此证明步骤依赖于模型域 $D=\{0,1\}$ 上等式的可判定性，即 `∀x,y∈D, (x=y) ∨ (x≠y)`。这在Coq或Lean等构造性逻辑系统中是成立的，因为 `D` 是一个有限类型。

*   **E. 具体化规则 (Reification Rule)**
    *   **(Reif)**: $\overline{\Gamma \vdash t \sim [t \equiv ()]}$。我们需要证明 $\Gamma \models t \sim [t \equiv ()]$。即：证明对任意估值 `ν`，`〚t〛_ν = 〚[t ≡ ()]〛_ν`。
        *   根据解释的定义，`〚[t ≡ ()]〛_ν` 的值为 `1` 当且仅当 `〚t〛_ν = 〚()〛_ν`，即 `〚t〛_ν = 1`。否则，其值为 `0`。
        *   因此，`〚[t ≡ ()]〛_ν` 的值总是等于 `〚t〛_ν` 在域 `{0, 1}` 中的值。等式成立。
所有规则都已验证。可靠性定理得证。 **Q.E.D.**

##### **5.1.3. 一致性结论**

**定理**: `CIE` 系统是一致的。具体而言，`∅ ⊢ ⟨()⟩ ~ ()` 是不可证的。

**证明**:
1.  **假设 `∅ ⊢ ⟨()⟩ ~ ()` 是可证的**。
2.  根据我们刚刚证明的**可靠性定理**，如果它是可证的，那么它必须在模型 `M` 中是有效的。即 `∅ ⊨ ⟨()⟩ ~ ()` 必须成立。
3.  根据语义后承的定义，`∅ ⊨ ⟨()⟩ ~ ()` 意味着对于**所有**估值 $\nu$，都必须有 $〚⟨()⟩〛_\nu = 〚()〛_\nu$。
4.  我们来计算这两边的值（注意它们不依赖于 $\nu$）：
    *   对于左侧，根据语法定义 1.4，项 `⟨()⟩` 是 `pair((), ())` 的语法糖。根据模型 `M` 的解释规则第3条（`〚\text{pair}(t₁, t₂)〛_ν := 0`），我们有 $〚⟨()⟩〛_\nu = 〚\text{pair}((), ())〛_\nu = \mathbf{0}$。
    *   对于右侧，根据解释规则第2条（`〚()〛_ν := 1`），我们有 $〚()〛_\nu = \mathbf{1}$。
5.  因此，`∅ ⊨ ⟨()⟩ ~ ()` 要求 `0 = 1`。这是一个**矛盾**。
6.  这个矛盾说明我们的初始假设（“`∅ ⊢ ⟨()⟩ ~ ()` 是可证的”）必定是错误的。

因此，`∅ ⊢ ⟨()⟩ ~ ()` 不可证。系统 `CIE` 存在不可证的判断，故其是一致的。

**Q.E.D.**

### **6. 非合流性与非终止性**

本节对CIE系统的两个关键计算性质——终止性和合流性——进行形式化分析与证明。

#### **6.1 非终止性 (Non-Termination)**

CIE系统不是强规范化的，即存在可以无限进行下去的计算。

**定理 6.1.1 (非终止性)**
CIE的迁移关系 `⟶` 不是终止的。

**证明.**
我们通过构造一个无限的计算序列来证明此定理。

1.  **设置**:
    *   设签名 $\Sigma$ 包含一个一元函数符号 `s`。
    *   考虑初始构型项 $C_0 := \langle [x \equiv s(x)], \langle\rangle \rangle$。
        *   该项是良构的，因为对于子项 $[x \equiv s(x)]$，我们有 $\mathsf{vars}(s(x)) = \{x\} \subseteq \{x\} = \mathsf{vars}(x)$，满足模式安全性约束。
    *   初始状态为 $S_0 = \langle C_0, U_0 \rangle$，其中 $U_0 = \mathsf{ExtractGroundTerms}(C_0) = \{()\}$。

2.  **归纳构造**:
    我们归纳地定义一个状态序列 $S_k = \langle C_k, U_k \rangle$ for $k \in \mathbb{N}$，并证明 $S_k \longrightarrow S_{k+1}$ 对所有 $k \ge 0$ 成立。

    *   **归纳假设 P(k)**: 状态 $S_k$ 具有如下形式：
        *   $C_k = \langle [x \equiv s(x)], s^k(()) \rangle$
        *   $U_k = \{ s^i(()) \mid 0 \le i \le k \}$
        (其中 $s^0(t) := t$ 且 $s^{i+1}(t) := s(s^i(t))$)

    *   **基础情形 (k=0)**:
        $S_0 = \langle \langle [x \equiv s(x)], () \rangle, \{()\} \rangle$。这与我们的初始状态定义一致，所以 P(0) 成立。

    *   **归纳步骤**:
        假设 P(k) 对某个 $k \ge 0$ 成立。我们证明存在一次合法的迁移 $S_k \longrightarrow S_{k+1}$ 且 $S_{k+1}$ 满足 P(k+1)。
        *   我们应用**模式应用 (Schema Application)** 规则到状态 $S_k = \langle C_k, U_k \rangle$。
        *   选择如下参数:
            1.  应用位置 $p_{app}$ 指向 $C_k$ 中的子项 $s^k(())$。因此，应用目标项 $a = s^k(())$。
            2.  公理模式位置 $p_{ax}$ 指向 $[x \equiv s(x)] \in \mathsf{Sub}(C_k)$。因此，$l=x, r=s(x)$。
            3.  替换 $\sigma_k: \{x\} \to T_\Sigma$ 定义为 $\sigma_k(x) := s^k(())$。
        *   验证规则条件:
            1.  $a = s^k(())$ 是基项。
            2.  $[x \equiv s(x)]$ 是含变量的子项。
            3.  $\mathsf{codom}(\sigma_k) = \{s^k(()) \}$. 根据归纳假设 P(k)，$s^k(()) \in U_k$，因此 $\mathsf{codom}(\sigma_k) \subseteq U_k$。
            4.  $a \approx_{C_k} \sigma_k(l)$ 成立，因为这等价于 $s^k(()) \approx_{C_k} s^k(())$，由自反性保证。
        *   所有条件满足，故可进行转换:
            *   $C_{k+1} := C_k[\sigma_k(r)]_{p_{app}} = C_k[s(s^k(()))]_{p_{app}} = \langle [x \equiv s(x)], s^{k+1}(()) \rangle$。
            *   $U_{k+1} := U_k \cup \mathsf{ExtractGroundTerms}(s^{k+1}(())) = U_k \cup \{s^{k+1}(()) \} = \{ s^i(()) \mid 0 \le i \le k+1 \}$。
        *   由此得到的状态 $S_{k+1} = \langle C_{k+1}, U_{k+1} \rangle$ 满足 P(k+1)。

3.  **结论**:
    通过数学归纳法，我们构造了一个无限的计算序列 $S_0 \longrightarrow S_1 \longrightarrow S_2 \longrightarrow \dots$。因此，CIE系统不是终止的。
    **Q.E.D.**

---
#### **6.2 非合流性 (Non-Confluence)**

CIE 系统不是合流的。存在一个状态 $S$，它可以归约到两个不同的范式 $S_1$ 和 $S_2$。我们通过构造一个具体的反例来证明这一点。

**定理 6.2.1 (非合流性)**
CIE 的迁移关系 `⟶` 不是合流的。

**证明.**
我们将构造一个初始状态 $S_0$，并展示存在两条不同的归约路径，分别通向两个不同的范式 $S_{A'}$ 和 $S_{B'}$。

##### **1. 证明策略与关键前提**
本证明的核心在于构造一个临界对（critical pair），其中一个**反射归约**和一个**模式应用**在同一个子项上竞争。我们将展示，根据选择的归约路径，系统的动态上下文 `Γ(C)` 会发生改变，从而永久性地关闭另一条路径的可能性。

本证明依赖于一个关键性质：对于特定的初始构型 $C_0$，其初始已知基项论域 $U_0 = \mathsf{ExtractGroundTerms}(C_0)$ **不包含** `()` 项。`ExtractGroundTerms` 函数（定义于 3.1 节）的这一特性是自然的，因为它只收集项中实际出现的基项子项。如果一个常量（如 `()`）没有在初始构型中明确写出，它就不会成为初始知识的一部分。

##### **2. 设置：初始状态**

设签名 $\Sigma$ 包含三个不同的常数（0-元函数符号）：`a`, `b`, `c`。

*   **初始构型项 ($C_0$):**
    $$ C_0 := \text{pair}(\underbrace{[a \equiv b]}_{\text{公理1}}, \text{pair}(\underbrace{[x \equiv c]}_{\text{公理2}}, \underbrace{[a \equiv b]}_{\text{应用目标}})) $$
    该构型是良构的，因为其唯一的模式 `[x ≡ c]` 满足模式安全性约束。

*   **初始已知基项论域 ($U_0$):**
    $U_0 = \mathsf{ExtractGroundTerms}(C_0)$。根据 `C₀` 的结构，它包含的基项子项有 `a`, `b`, `c`, `[a ≡ b]` 等，但**不包含**独立的 `()` 项。因此，`() ∉ U_0`。

*   **初始状态 ($S_0$):**
    $S_0 = \langle C_0, U_0 \rangle$。

##### **3. 分析初始状态 $S_0$ 与分叉点**

在状态 $S_0$ 下，动态上下文 `Γ(C₀)` 包含两个判断 `(a,b)` 和一个判断 `(x,c)`。基础等式集 `E_{C₀}` 因此包含 `(a,b)`。这直接导致 **`a ≈_{C₀} b`** 成立。

位于位置 `2.2` 的子项 `[a ≡ b]` 成为一个分叉点：
*   **路径 A (反射归约)**: 由于 `a ≈_{C₀} b`，该子项可以被归约为 `()`。
*   **路径 B (模式应用)**: 该子项是一个基项，可以被公理模式 `[x ≡ c]` 匹配和重写。

##### **4. 路径 A: 优先进行反射归约**

对位置 `2.2` 的 `[a ≡ b]` 应用**反射归约**规则。
*   **迁移**: $S_0 \longrightarrow S_A = \langle C_A, U_A \rangle$，其中
    *   $C_A := \text{pair}([a \equiv b], \text{pair}([x \equiv c], ()))$
    *   $U_A := U_0$
*   在状态 $S_A$ 中，`a ≈_{C_A} b` 依然成立（因为 `[a ≡ b]` 仍在 `C_A` 中）。我们对位置 `1` 的 `[a ≡ b]` 进行第二次反射归约。
*   **迁移**: $S_A \longrightarrow S_{A'} = \langle C_{A'}, U_{A'} \rangle$，其中
    *   $C_{A'} := \text{pair}((), \text{pair}([x \equiv c], ()))$
    *   $U_{A'} := U_0$

**状态 $S_{A'}$ 是一个范式。**
*   **(反射归约)** 不适用：`C_{A'}` 中唯一的 `≡` 子项 `[x ≡ c]` 含有变量，不是基项。
*   **(冗余消除)** 不适用：`C_{A'}` 中没有 `(... ≡ ())` 形式的子项。
*   **(模式应用)** 不适用：唯一的模式是 `[x ≡ c]`。`C_{A'}` 中的基项子项只有 `()`。要应用模式，需要构造替换 $\sigma = \{x \mapsto ()\}$. 然而，此规则要求 `codom(σ) ⊆ U_{A'}`。由于 `()` 不是 `C₀` 的子项，根据**引理 3.1.1**，我们有 `() ∉ U₀ = U_{A'}`。因此该替换**非法**，无法应用。

##### **5. 路径 B: 优先进行模式应用**

使用模式 `[x ≡ c]` 重写位置 `2.2` 的子项 `[a ≡ b]`。
*   **条件**: 目标 `a_{target} = [a ≡ b]`。替换 $\sigma = \{x \mapsto [a \equiv b]\}$。`codom(σ) = \{[a ≡ b]\} ⊆ U_0`，合法。匹配条件 `a_{target} ≈_{C₀} σ(x)` 因自反性成立。
*   **迁移**: $S_0 \longrightarrow S_B = \langle C_B, U_B \rangle$，其中
    *   $C_B := \text{pair}([a \equiv b], \text{pair}([x \equiv c], c))$
    *   $U_B := U_0$
*   在状态 $S_B$ 中，`a ≈_{C_B} b` 依然成立。我们对位置 `1` 的 `[a ≡ b]` 进行反射归约。
*   **迁移**: $S_B \longrightarrow S_{B'} = \langle C_{B'}, U_{B'} \rangle$，其中
    *   $C_{B'} := \text{pair}((), \text{pair}([x \equiv c], c))$
    *   $U_{B'} := U_0$

**状态 $S_{B'}$ 是一个范式。**
*   **(反射归约)** / **(冗余消除)** 不适用。
*   **(模式应用)** 不适用：唯一的模式是 `[x ≡ c]`。基项子项是 `()` 和 `c`。
    *   对 `()` 应用：不合法，因为 `() ∉ U_0` (由**引理 3.1.1**)。
    *   对 `c` 应用：可构造合法替换 $\sigma = \{x \mapsto c\}$ (因 $c \in U_0$) 。应用会重写 `c` 为 `σ(c) = c`。这是一个到自身状态的平凡迁移。根据我们**4.2节**的范式定义，由于不存在到**不同**状态的迁移，`S_{B'}` 是一个范式。

##### **6. 结论**
我们从状态 $S_0$ 出发，存在两条不同的归约路径，分别终止于两个不同的范式 $S_{A'}$ 和 $S_{B'}$：
*   $C_{A'} = \text{pair}((), \text{pair}([x \equiv c], ()))$
*   $C_{B'} = \text{pair}((), \text{pair}([x \equiv c], c))$
由于 $C_{A'} \neq C_{B'}$，这两个范式是不同的。这证明了 CIE 系统的迁移关系 `⟶` 不是合流的。
**Q.E.D.**

#### **6.3 非合流性的另一个证明**

CIE 系统不是合流的。存在一个状态 $S$，它可以归约到两个不同的范式 $S_1$ 和 $S_2$。我们通过构造一个具体的反例来证明这一点。

**定理 6.2.1 (非合流性)**
CIE 的迁移关系 `⟶` 不是合流的。

**证明.**
我们将构造一个初始状态 $S_0$，并展示存在两条不同的归约路径，分别通向两个不同的范式 $S_A'$ 和 $S_B'$。

##### **1. 证明策略与关键机制**
本证明的核心在于构造一个临界对（critical pair），其中一个**反射归约 (Reflection Reduction)** 和一个**模式应用 (Schema Application)** 之间存在根本性的竞争。与依赖于已知基项论域 `U` 内容的脆弱反例不同，本证明利用了CIE一个更为内在的机制：**构型项 `C` 的变化会直接导致动态上下文 `Γ(C)` 的变化，从而改变操作同余关系 `≈_C` 的定义**。

我们将展示，根据选择的归约路径，一个关键的公理可以被提前从 `Γ(C)` 中移除，从而永久性地阻止另一条路径上本可能发生的归约。这种基于动态上下文演化的分歧，是系统非合流性的一个根本原因。

##### **2. 设置：初始状态**

设签名 $\Sigma$ 包含三个不同的常数（0-元函数符号）：`a`, `b`, `c`。

*   **初始构型项 ($C_0$):**
    $$ C_0 := \text{pair}(\underbrace{[a \equiv b]}_{\text{公理1}}, \text{pair}(\underbrace{[b \equiv c]}_{\text{公理2}}, \underbrace{a}_{\text{应用目标}})) $$
    该构型是良构的，因其所有含变量的子项（此处为空）均满足模式安全性约束。

*   **初始状态 ($S_0$):**
    $S_0 = \langle C_0, \mathsf{ExtractGroundTerms}(C_0) \rangle$。

##### **3. 分析初始状态 $S_0$ 与分叉点**

在状态 $S_0$ 下，动态上下文 `Γ(C₀)` 包含判断 `(a,b)` 和 `(b,c)`。
*   由于 `(a,b)` 来自 `C₀` 中一个不含变量的子项 `[a ≡ b]`，它直接贡献 `(a,b)` 到基础等式集 `E_{C₀}` 中。
*   这直接导致 **`a ≈_{C₀} b`** 成立。

此时，系统面临一个选择，形成了分叉点：
*   **路径 A (反射归约)**: 位于位置 `1` 的子项 `[a ≡ b]` 满足反射归约的条件，因为 `a ≈_{C₀} b`。
*   **路径 B (模式应用)**: 位于位置 `2.2` 的子项 `a` 可以作为模式应用的目标。公理模式来自位置 `2.1` 的 `[b ≡ c]`（即 `l=b, r=c`）。其应用条件 `a ≈_{C₀} σ(l)` 变为 `a ≈_{C₀} b`（因`σ`为空替换），此条件恰好成立。

##### **4. 路径 A: 优先进行反射归约**

对位置 `1` 的 `[a ≡ b]` 应用**反射归约**规则。
*   **迁移**: $S_0 \longrightarrow S_A = \langle C_A, U_A \rangle$，其中
    *   $C_A := \text{pair}((), \text{pair}([b \equiv c], a))$
    *   $U_A := \mathsf{ExtractGroundTerms}(C_0)$
*   **状态 $S_A$ 的分析**:
    在 $S_A$ 中，构型项 `C_A` 不再包含子项 `[a ≡ b]`。因此，动态上下文 `Γ(C_A)` **不再包含判断 `(a,b)`**。由于没有其他公理可以推导出 `a` 与 `b` 等价，我们有 **`a <binary data, 3 bytes>_{C_A} b`**。
    此时，原本在路径 B 中可能的模式应用（重写 `a`）变得不再可能，因为其匹配条件 `a ≈_{C_A} b` 不再满足。
    $C_A$ 中没有其他可应用的归约规则。

**状态 $S_A$ 是一个范式。**
*   **(反射归约)** 不适用：`C_A` 中唯一的 `≡` 子项 `[b ≡ c]` 对应 `b ≈_{C_A} c` 不成立。
*   **(模式应用)** 不适用：如上分析，匹配 `a` 的条件已失效。
*   **(冗余消除)** 不适用。
因此，`S_A` 是路径A的终点，我们称 $S_A' = S_A$。

##### **5. 路径 B: 优先进行模式应用**

使用位置 `2.1` 的模式 `[b ≡ c]` 重写位置 `2.2` 的子项 `a`。
*   **条件**: 目标 `a_{target} = a`。模式 `l=b, r=c`。匹配条件 `a_{target} ≈_{C₀} b` 成立。
*   **迁移**: $S_0 \longrightarrow S_B = \langle C_B, U_B \rangle$，其中
    *   $C_B := \text{pair}([a \equiv b], \text{pair}([b \equiv c], c))$
    *   $U_B := \mathsf{ExtractGroundTerms}(C_0) \cup \{c\}$
*   **状态 $S_B$ 的分析**:
    在状态 $S_B$ 中，子项 `[a ≡ b]` 仍然存在，因此 `a ≈_{C_B} b` 仍然成立。我们可以对位置 `1` 的 `[a ≡ b]` 进行反射归约。
*   **迁移**: $S_B \longrightarrow S_{B'} = \langle C_{B'}, U_{B'} \rangle$，其中
    *   $C_{B'} := \text{pair}((), \text{pair}([b \equiv c], c))$
    *   $U_{B'} := U_B$

**状态 $S_{B'}$ 是一个范式。**
*   **(反射归约)** 不适用：`C_{B'}` 中唯一的 `≡` 子项 `[b ≡ c]` 对应 `b ≈_{C_B'} c` 不成立。
*   **(模式应用)** 不适用：模式为 `[b ≡ c]`，但 `C_{B'}` 中没有合适的基项目标可以与之匹配。
*   **(冗余消除)** 不适用。

##### **6. 结论**
我们从状态 $S_0$ 出发，存在两条不同的归约路径，分别终止于两个不同的范式 $S_A'$ 和 $S_{B'}$：
*   $S_A' = \langle \text{pair}((), \text{pair}([b \equiv c], a)), U_A \rangle$
*   $S_{B'} = \langle \text{pair}((), \text{pair}([b \equiv c], c)), U_{B'} \rangle$

由于其构型项 $C_A' = \text{pair}((), \text{pair}([b \equiv c], a))$ 和 $C_{B'} = \text{pair}((), \text{pair}([b \equiv c], c))$ 明显不同，这两个范式是不同的。这证明了 CIE 系统的迁移关系 `⟶` 不是合流的。

**Q.E.D.**

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

### **8. 可判定性与对象层反射**

**形式化前提:** 本节的证明依赖于标准的**同余闭包 (Congruence Closure)** 算法的正确性和终止性。

#### 定理 A（运行时操作同余的可判定性）

**设定.**

*   设 $\Sigma$ 为有限签名；$T_\Sigma$ 为其上所有**基项**（无变量项）的集合。
*   状态 $S=\langle C,U\rangle$ 按 §3 定义，且 $C$ 良构（§3.2），$U\subseteq T_\Sigma$ 有限。
*   动态上下文 $\Gamma(C)$、基础等式集 $E_C$ 与操作同余关系 $\approx_C$ 按 §3.3 定义：
    $$ \Gamma(C)\;:=\;\{(l,r)\mid (l\equiv r)\in \mathsf{Sub}(C)\} $$
    $$ E_C\;:=\;\{(\sigma(l),\sigma(r))\mid (l,r)\in\Gamma(C),\ \sigma:\mathsf{vars}(l)\to U\} $$
    $$ \approx_C\;=\;\text{由 }E_C\text{ 生成的 }T_\Sigma\text{ 上的最小同余关系。} $$

**命题.**

存在一个**全定义可计算**函数
$$ \mathrm{dec}_{\approx}:\ \mathsf{States}\times T_\Sigma\times T_\Sigma\to\{0,1\} $$
使得对所有良构状态 $S=\langle C,U\rangle$ 与所有 $t_1,t_2\in T_\Sigma$，
$$ \mathrm{dec}_{\approx}(S,t_1,t_2)=1\quad\Longleftrightarrow\quad t_1\approx_C t_2. $$
##### **证明**

为了证明此定理，我们需要构造一个算法，该算法接收一个状态 $S=\langle C,U\rangle$ 和两个基项 $t_1, t_2$ 作为输入，并且保证在有限时间内终止，输出 `1` 当且仅当 $t_1 \approx_C t_2$ 成立。

我们将证明分为两个主要部分：
1.  **基础等式集 $E_C$ 的有限性与可计算性**：证明对于任何给定的状态 $S=\langle C,U\rangle$，基础等式集 $E_C$ 不仅是有限的，而且可以被算法有效地构造出来。
2.  **同余关系的可判定性**：证明对于一个有限的基础等式集 $E_C$，其在基项集合 $T_\Sigma$ 上生成的同余关系 $\approx_C$ 是可判定的。我们将通过应用经典的**同余闭包 (Congruence Closure)** 算法来完成此证明。

---

###### **第一部分：$E_C$ 的有限性与可计算性**

根据定义：
$$ E_C\;:=\;\{(\sigma(l),\sigma(r))\mid (l,r)\in\Gamma(C),\ \sigma:\mathsf{vars}(l)\to U\} $$
其中 $\Gamma(C)$ 是从构型项 $C$ 中提取的公理模式。

**步骤 1: 构造 $\Gamma(C)$**

*   **输入**: 构型项 $C$。
*   **过程**:
    1.  遍历 $C$ 的所有子项。由于 $C$ 是一个有限的树形结构，其子项集合是有限的。此遍历过程是可计算且终止的。
    2.  对于每一个子项 $s$，检查它是否具有 `(l ≡ r)` 的形式。
    3.  如果形式匹配，计算其变量集合 $\mathsf{vars}(s)$。此过程也是可计算的。
    4.  如果 $\mathsf{vars}(s) \neq \emptyset$，则将序对 `(l, r)` 添加到集合 $\Gamma(C)$ 中。
*   **结论**: 由于 $C$ 是有限的，其子项数量有限，因此 $\Gamma(C)$ 是一个**有限集**，并且上述构造过程是一个终止的算法。

**步骤 2: 构造 $E_C$**

*   **输入**: 有限集 $\Gamma(C)$ 和有限的已知基项论域 $U$。
*   **过程**:
    1.  初始化一个空集 $E_C$。
    2.  对 $\Gamma(C)$ 中的每一个公理模式 $(l,r)$ 进行迭代：
        a. 确定 $l$ 中的变量集合 $V_l = \mathsf{vars}(l)$。设其大小为 $k = |V_l|$。
        b. $U$ 是一个有限集合。设其大小为 $m = |U|$。
        c. 构造从 $V_l$到 $U$ 的所有可能替换 $\sigma$ 的集合。一个替换 $\sigma$ 是一个从 $V_l$ 到 $U$ 的函数。这种函数的总数是 $m^k$。这是一个**有限**的数字。
        d. 对这 $m^k$ 个替换中的每一个 $\sigma$：
            i.  计算基项 $\sigma(l)$ 和 $\sigma(r)$。项的替换是一个标准的、可计算的操作。
            ii. 将序对 $(\sigma(l), \sigma(r))$ 添加到集合 $E_C$ 中。
*   **结论**: 由于 $\Gamma(C)$ 是有限的，并且对于其中每个模式，可能的替换数量也是有限的，所以最终生成的集合 $E_C$ 是一个**有限的基项等式集**。整个构造过程是一个终止的算法。

至此，我们已经证明了可以将问题 `t₁ ≈_C t₂` 的判定，归约到一个更标准的问题：给定一个有限的基项等式集 $E_C$ 和两个查询基项 $t_1, t_2$，判定 $t_1$ 和 $t_2$ 在由 $E_C$ 生成的同余关系下是否等价。

---

###### **第二部分：同余关系的可判定性 (同余闭包算法)**

关系 $\approx_C$ 被定义为包含 $E_C$ 的**最小**同余关系。判定两个项在此关系下是否等价，是计算理论中的一个经典问题，可以通过**同余闭包 (Congruence Closure)** 算法高效解决。

**步骤 3: 确定相关项的有限宇宙**

尽管 $\approx_C$ 定义在无限的基项集合 $T_\Sigma$ 上，但要判定两个特定的基项 $t_1$ 和 $t_2$ 是否等价，我们只需要考虑一个有限的项子集。

1.  令 $T_{E_C}$ 为所有出现在 $E_C$ 中的项（即所有 $\sigma(l)$ 和 $\sigma(r)$）的集合。
2.  令 $\mathsf{Sub}(S)$ 为 $S$ 中所有项的子项集合。
3.  定义相关项的宇宙 $\mathcal{T}$ 为：
    $$ \mathcal{T} := \mathsf{Sub}(T_{E_C}) \cup \mathsf{Sub}(t_1) \cup \mathsf{Sub}(t_2) $$
    由于 $E_C$, $t_1$, $t_2$ 都是有限的，它们包含的子项数量也是有限的。因此，$\mathcal{T}$ 是一个**有限的基项集合**。

任何关于 $t_1 \approx_C t_2$ 的证明，都只可能涉及到 $\mathcal{T}$ 中的项以及由它们通过函数符号构造的项。同余闭包算法正是利用了这一性质，在有限的宇宙 $\mathcal{T}$ 上进行操作。

**步骤 4: 应用同余闭包算法**

*   **输入**: 有限的项宇宙 $\mathcal{T}$ 和有限的等式集 $E_C$。
*   **算法概述**: (例如，基于并查集优化的 Downey-Sethi-Tarjan 算法)
    1.  **初始化**: 为 $\mathcal{T}$ 中的每一个项 $t$ 创建一个集合 $\{t\}$，形成对 $\mathcal{T}$ 的一个划分。这可以用一个**并查集 (Union-Find)** 数据结构来表示，其中每个项最初都在其自己的等价类中。
    2.  **处理等式**: 对 $E_C$ 中的每一个等式 $(a, b)$，执行 `union(a, b)` 操作，合并 $a$ 和 $b$ 所在的等价类。
    3.  **闭包**: 重复以下步骤直到没有变化发生（即达到不动点）：
        *   在 $\mathcal{T}$ 中寻找两个项 $u, v$，它们具有形式 $u = f(u_1, \dots, u_n)$ 和 $v = f(v_1, \dots, v_n)$。
        *   如果对于所有的 $i=1, \dots, n$，`find(uᵢ) == find(vᵢ)`（即 $u_i$ 和 $v_i$ 在当前的等价类划分中等价），但是 `find(u) != find(v)`。
        *   则执行 `union(u, v)` 操作。
        由于 $\mathcal{T}$ 是有限的，`union` 操作的次数有上限（最多 $|\mathcal{T}|-1$ 次），因此这个闭包过程保证终止。
*   **判定**: 算法终止后，我们得到了 $E_C$ 在 $\mathcal{T}$ 上的同余闭包。要判定 $t_1 \approx_C t_2$ 是否成立，只需检查 $t_1$ 和 $t_2$ 在最终的并查集结构中是否属于同一个等价类，即计算 `find(t₁) == find(t₂)`。

**步骤 5: 整合为 `dec_≈` 函数**

我们可以将以上所有步骤整合为一个完整的算法 `dec_≈(S, t₁, t₂)`:

1.  从 $S = \langle C, U \rangle$ 计算出有限集 $\Gamma(C)$。
2.  从 $\Gamma(C)$ 和 $U$ 计算出有限的基项等式集 $E_C$。
3.  构造有限的项宇宙 $\mathcal{T} = \mathsf{Sub}(E_C) \cup \mathsf{Sub}(t_1) \cup \mathsf{Sub}(t_2)$。
4.  在 $\mathcal{T}$ 和 $E_C$ 上运行同余闭包算法。
5.  如果最终 `find(t₁) == find(t₂)`，则返回 `1`；否则返回 `0`。

由于该算法的每一步都是可计算且必定终止的，因此它定义了一个**全定义可计算函数**。

---

##### **结论**

我们已经成功地描述了一个算法，该算法能在有限时间内判定任何给定的良构状态 $S=\langle C,U\rangle$ 下任意两个基项 $t_1, t_2$ 之间的操作同余关系 $t_1\approx_C t_2$。这个算法的存在性证明了函数 $\mathrm{dec}_{\approx}$ 的存在性与可计算性。

因此，定理 A 得证。

**Q.E.D.**

---

#### 定理 B（对象层反射：双向桥梁与具体化）

为清晰起见，定理 B 分为两个互补的形式命题 B1 与 B2。

##### 定理 B1（内化等价与外部等价的对象层等价）

对任意上下文 $\Gamma$ 与任意项 $t_1,t_2\in T_\Sigma(V)$，

$$

\Gamma\vdash t_1\sim t_2\quad\Longleftrightarrow\quad \Gamma\vdash (t_1\equiv t_2)\sim().

$$

**形式依据.**

* “$\Rightarrow$” 由规则 **(Equiv-Reflection)**：$\dfrac{\Gamma\vdash t_1\sim t_2}{\Gamma\vdash (t_1\equiv t_2)\sim()}$。

* “$\Leftarrow$” 由规则 **(Equiv-Elim)**：$\dfrac{\Gamma\vdash (t_1\equiv t_2)\sim()}{\Gamma\vdash t_1\sim t_2}$。

该命题表明：**无需引入元层**，对象语言内部即可将“外部等价判断”与“内化的等价断言为真”在推导上严格对齐。

##### 定理 B2（对象层具体化/再化）

对任意上下文 $\Gamma$ 与任意项 $t\in T_\Sigma(V)$，

$$

\Gamma\vdash t\sim (t\equiv()).

$$

**形式依据.**

* 直接由零前提规则 **(Reif)**：$\overline{\Gamma\vdash t\sim (t\equiv())}$。

---

以上两条定理分别刻画了 CIE 的两项关键独特性质：

* **A**：把“有限运行时知识域 $U$”与同余闭包绑定，从而在**系统规则层**保证了等价判定的可判定性。

* **B**：在**对象层内部**建立“外部等价 ⇄ 内化等价为真”的**双向桥梁**，并提供对任意项的“自反具体化”判断，无需借助任何元逻辑。


