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

##### **1.5. 变量、替换**

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