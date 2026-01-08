### **结构化真理逻辑 (Structured Truth Logic, STL) 的形式化定义**

#### **1. 语法 (Syntax)**

系统的语言 $L_{STL}$ 由一组良构的**项 (Term)** 构成。项的定义基于 S-表达式结构。

##### **1.1. 字母表 (Alphabet)**

$L_{STL}$ 的字母表 $\Sigma$ 由以下不相交的集合构成：
*   **变量 (Variables)**: 一个可数无限集 $V = \{p, q, r, p_0, p_1, \dots\}$。
*   **常量 (Constants)**: 一个有限集 $C = \{ T, F, \text{Quote}, \text{TA}, \text{NEG} \}$。
*   **括号 (Parentheses)**: `(` 和 `)`。

##### **1.2. 项的构造规则 (Term Formation Rules)**

项的集合 $\mathcal{T}$ 是满足以下规则的最小集合：

1.  **原子 (Atom)**: 如果 $a \in V \cup C$，那么 $a$ 是一个项。
2.  **列表 (List)**: 如果 $t_1, t_2, \dots, t_n$ ($n \ge 0$) 都是项，那么 $(t_1 \ t_2 \ \dots \ t_n)$ 也是一个项。空列表 `()` 也是一个合法的项。

*注：形如 `(TA P)`、`(NEG P)` 和 `(Quote S)` 的表达式是**列表**这一构造规则的特例，其中列表的第一个元素分别是常量 `TA`、`NEG` 和 `Quote`。*

#### **2. 判断 (Judgement)**

本系统仅有一种判断形式，即**同余判断 (Congruence Judgement)**，其形式为：
$$
A \equiv B
$$
其中 $A$ 和 $B$ 都是 $L_{STL}$ 中的项。该判断意为“项 $A$ 和项 $B$ 是可证等价的”。

#### **3. 公理与推理规则 (Axioms and Inference Rules)**

一个判断 $A \equiv B$ 是可证明的，当且仅当它可以从以下公理模式和推理规则推导得出。

##### **A. 同余关系的基本规则**

这些规则确保 $\equiv$ 是一个同余关系。

*   **自反律 (Reflexivity):**
    $$ \overline{A \equiv A} $$

*   **对称律 (Symmetry):**
    $$ \frac{A \equiv B}{B \equiv A} $$

*   **传递律 (Transitivity):**
    $$ \frac{A \equiv B, \quad B \equiv C}{A \equiv C} $$

*   **同余律 (Congruence):**
    此规则保证了在列表结构中，等价的项可以互相替换。
    $$ \frac{A_1 \equiv B_1, \quad \dots, \quad A_n \equiv B_n}{(A_1 \ \dots \ A_n) \equiv (B_1 \ \dots \ B_n)} $$

##### **B. 真理断言的结构规则 (Rules for Truth Assertion)**

*   **规则 TR-1 (Idempotence of TA):**
    $$ \overline{(TA \ (TA \ P)) \equiv (TA \ P)} $$

*   **规则 TR-2 (Truth Criterion):**
    $$ \frac{(TA \ P) \equiv T}{P \equiv T} $$

*   **规则 TR-3 (Data/Structure Distinction):**
    $$ \overline{(TA \ (Quote \ S)) \equiv (Quote \ S)} $$

##### **C. 否定与矛盾规则 (Rules for Negation and Contradiction)**

*   **公理 NEG-1 (Negation of Truth):**
    $$ \overline{(NEG \ T) \equiv (Quote \ F)} $$

*   **规则 CON-1 (Principle of Explosion):**
    对于任意项 $A$ 和 $B$：
    $$ \frac{P \equiv T, \quad (NEG \ P) \equiv T}{A \equiv B} $$


### 模型论和元理论性质
#### **1. STL 的模型 (Model for STL)**

为了解释 STL 的语义，我们构建一个**项重写模型 (Term Rewriting Model)**。在这个模型中，一个项的“意义”就是它经过一系列确定的化简规则后达到的最终形式，我们称之为**范式 (Normal Form)**。

##### **1.1. 语义域 (Semantic Domain)**

我们的语义域就是项的集合 $\mathcal{T}$ 本身。我们不将项映射到某个外部的数学结构，而是将其映射到 $\mathcal{T}$ 中的一个子集，即范式项的集合。

##### **1.2. 求值函数 (Evaluation Function)**

我们定义一个求值函数 `eval: T -> T`，它将任意一个项映射到其唯一的范式。`eval(A)` 的计算方式如下：

1.  **递归地**对项 `A` 的所有子项进行求值。
2.  将求值后的子项重新组合。
3.  对重组后的项应用一组**化简规则 (Simplification Rules)**，直到无法再应用任何规则为止。

这个过程保证了 `eval(A)` 的结果是一个无法再被化简的项，即范ax式。

**化简规则集 $\mathcal{S}$：**

我们根据系统中的公理来定义化简规则。一个项 `X` 被化简为 `Y`，记为 `X ↦ Y`。

*   **(S1)** `(TA T) ↦ T`
    *   *动机：这是规则 TR-2 的一个方向。断言“真”为“真”，其结果就是“真”。*
*   **(S2)** `(TA (TA P)) ↦ (TA P)`
    *   *动机：公理 TR-1 (Idempotence of TA)。*
*   **(S3)** `(TA (Quote S)) ↦ (Quote S)`
    *   *动机：公理 TR-3 (Data/Structure Distinction)。*
*   **(S4)** `(NEG T) ↦ (Quote F)`
    *   *动机：公理 NEG-1 (Negation of Truth)。*

**`eval` 函数的精确定义：**

1.  如果 `A` 是一个原子 (即 $A \in V \cup C$)，则 `eval(A) = A`。
2.  如果 `A` 是一个列表 $(t_1 \ \dots \ t_n)$，则 `eval(A)` 的计算步骤如下：
    a.  计算所有子项的范式：$t'_i = \text{eval}(t_i)$。
    b.  构造新列表 $A' = (t'_1 \ \dots \ t'_n)$。
    c.  将化简规则集 $\mathcal{S}$ 反复应用于 $A'$ 及其子结构，直到无法再应用为止。这个最终结果就是 `eval(A)`。
    
    *例如，`eval((TA (TA T)))` 的计算过程是：*
    *   *内层 `eval(T)` 结果是 `T`。*
    *   *中层 `eval((TA T))` 变为 `(TA T)`，应用规则 S1 化简为 `T`。*
    *   *外层 `eval((TA T))` 再次应用规则 S1 化简为 `T`。*
    *   *所以 `eval((TA (TA T))) = T`。*

##### **1.3. 语义有效性 (Semantic Validity)**

我们定义模型中的“语义等价”关系 `⊨` 如下：
$$
A \models B \quad \text{当且仅当} \quad \text{eval}(A) = \text{eval}(B)
$$
这里的 ` = ` 是指两个项在语法上完全相同。

如果对于任意的项 $A$ 和 $B$，只要 $A \equiv B$ 在 STL 中是可证的，就有 $A \models B$ 在我们的模型中成立，那么这个模型就是**可靠的 (Sound)**。

---

#### **2. 可靠性证明 (Proof of Soundness)**

**定理：STL 是可靠的。**

**证明：** 我们需要证明，如果一个判断 $A \equiv B$ 可以通过 STL 的公理和规则推导出来（记为 $\vdash A \equiv B$），那么在我们的模型中必然有 $A \models B$（即 $\text{eval}(A) = \text{eval}(B)$）。

我们对推导的长度进行结构归纳。

##### **基础步骤：公理**

我们需要证明所有公理在模型中都成立。

1.  **自反律:** $\vdash A \equiv A$。
    *   模型检验：显然，$\text{eval}(A) = \text{eval}(A)$。**成立**。

2.  **TR-1:** $\vdash (TA \ (TA \ P)) \equiv (TA \ P)$。
    *   模型检验：我们需要证明 $\text{eval}((TA \ (TA \ P))) = \text{eval}((TA \ P))$。
    *   设 $P_n = \text{eval}(P)$。
    *   RHS (右侧): $\text{eval}((TA \ P)) = \text{eval}((TA \ P_n))$。根据 $P_n$ 的形式，有几种情况：
        *   若 $P_n = T$，则 RHS = `eval((TA T))` = `T` (据 S1)。
        *   若 $P_n = (Quote \ S')$，则 RHS = `eval((TA (Quote S')))` = `(Quote S')` (据 S3)。
        *   否则，RHS = `(TA P_n)`。
    *   LHS (左侧): $\text{eval}((TA \ (TA \ P))) = \text{eval}((TA \ \text{eval}((TA \ P))))$。
        *   若 $P_n = T$，则 $\text{eval}((TA \ P)) = T$。LHS = `eval((TA T))` = `T`。与 RHS 相等。
        *   若 $P_n = (Quote \ S')$，则 $\text{eval}((TA \ P)) = (Quote \ S')$。LHS = `eval((TA (Quote S')))` = `(Quote S')`。与 RHS 相等。
        *   否则，$\text{eval}((TA \ P)) = (TA \ P_n)$。LHS = `eval((TA \ (TA \ P_n)))`，根据化简规则 S2，结果为 `(TA P_n)`。与 RHS 相等。
    *   在所有情况下，LHS 和 RHS 的求值结果都相同。**成立**。

3.  **TR-3:** $\vdash (TA \ (Quote \ S)) \equiv (Quote \ S)$。
    *   模型检验：设 $S_n = \text{eval}(S)$。
    *   LHS = `eval((TA (Quote S)))` = `eval((TA (Quote S_n)))`。根据化简规则 S3，结果为 `(Quote S_n)`。
    *   RHS = `eval((Quote S))` = `(Quote S_n)`。
    *   两者相等。**成立**。

4.  **NEG-1:** $\vdash (NEG \ T) \equiv (Quote \ F)$。
    *   模型检验：
    *   LHS = `eval((NEG T))`。根据化简规则 S4，结果为 `(Quote F)`。
    *   RHS = `eval((Quote F))` = `(Quote F)`。
    *   两者相等。**成立**。

##### **归纳步骤：推理规则**

假设所有前提在模型中都成立，我们需要证明结论也成立。

1.  **对称律:** 如果 $\vdash A \equiv B$ 且模型满足 $A \models B$，则 $\text{eval}(A) = \text{eval}(B)$。那么显然 $\text{eval}(B) = \text{eval}(A)$，即 $B \models A$。**成立**。

2.  **传递律:** 如果 $\vdash A \equiv B, \vdash B \equiv C$ 且模型满足 $A \models B, B \models C$，则 $\text{eval}(A) = \text{eval}(B)$ 且 $\text{eval}(B) = \text{eval}(C)$。根据等号的传递性，$\text{eval}(A) = \text{eval}(C)$，即 $A \models C$。**成立**。

3.  **同余律:** 假设 $\vdash A_i \equiv B_i$ 对于所有 $i=1,\dots,n$ 成立，且模型满足 $A_i \models B_i$，即 $\text{eval}(A_i) = \text{eval}(B_i)$。
    *   我们需要证明 $(A_1 \ \dots \ A_n) \models (B_1 \ \dots \ B_n)$。
    *   $\text{eval}((A_1 \ \dots \ A_n))$ 的计算是先得到 $(\text{eval}(A_1) \ \dots \ \text{eval}(A_n))$，然后化简。
    *   $\text{eval}((B_1 \ \dots \ B_n))$ 的计算是先得到 $(\text{eval}(B_1) \ \dots \ \text{eval}(B_n))$，然后化简。
    *   由于 $\text{eval}(A_i) = \text{eval}(B_i)$，两边在化简前得到的列表是完全相同的。因此，最终的化简结果也必然相同。**成立**。

4.  **TR-2 (Truth Criterion):** 假设 $\vdash (TA \ P) \equiv T$，且模型满足 $(TA \ P) \models T$，即 $\text{eval}((TA \ P)) = \text{eval}(T) = T$。
    *   我们需要证明 $P \models T$，即 $\text{eval}(P) = T$。
    *   根据 `eval` 的定义，$\text{eval}((TA \ P)) = \text{eval}((TA \ \text{eval}(P)))$。
    *   我们知道 $\text{eval}((TA \ \text{eval}(P))) = T$。
    *   让我们检查化简规则。要使一个形如 `(TA X)` 的项化简为 `T`，根据规则 S1，`X` 必须是 `T`。
    *   因此，必然有 $\text{eval}(P) = T$。**成立**。

5.  **CON-1 (Principle of Explosion):** 假设 $\vdash P \equiv T$ 和 $\vdash (NEG \ P) \equiv T$。根据归纳假设，模型满足 $P \models T$ 和 $(NEG \ P) \models T$。这意味着：
    a.  $\text{eval}(P) = T$
    b.  $\text{eval}((NEG \ P)) = T$
    *   我们需要证明对于任意 $A, B$，都有 $A \models B$，即 $\text{eval}(A) = \text{eval}(B)$。
    *   这是一个条件语句：如果前提在模型中为真，那么结论也必须为真。
    *   让我们来分析这个前提：
        *   从 (a)，我们有 $\text{eval}(P) = T$。
        *   将此代入 (b)：$\text{eval}((NEG \ P)) = \text{eval}((NEG \ \text{eval}(P))) = \text{eval}((NEG \ T))$。
        *   根据化简规则 S4，$\text{eval}((NEG \ T)) = (Quote \ F)$。
        *   所以，前提条件 (a) 和 (b) 在模型中同时成立，意味着 $T = (Quote \ F)$。
    *   但是，项 `T` 是一个原子，而项 `(Quote F)` 是一个列表。它们在语法上是不同的。因此，在我们的模型中，$T = (Quote \ F)$ 是**假**的。
    *   这意味着 CON-1 的前提条件在我们的模型中**永远不可能被满足**。
    *   在逻辑中，如果一个蕴含式的前提为假，则该蕴含式本身为真（*ex falso quodlibet*）。因此，CON-1 这条规则在我们的模型中是**有效（vacuously true）**的。**成立**。

我们已经证明了所有的公理和推理规则都在我们的模型中是有效的。因此，通过对推导的结构归纳，任何在 STL 中可证的同余判断 `A ≡ B` 在我们的模型中都成立。

**结论：STL 系统相对于我们构建的项重写模型是可靠的。**

---

#### **3. 一致性证明 (Proof of Consistency)**

一个形式系统是一致的，如果它不能证明所有命题。在 STL 的语境下，一致性意味着存在某些项 $A$ 和 $B$，使得 $A \equiv B$ 是**不可证明的**。如果系统是不一致的，那么根据爆炸原理（CON-1），任何 $A \equiv B$ 都将是可证的。

**定理：STL 是**一致的**。**

**证明：** 我们将通过反证法，并利用刚刚证明的可靠性定理来证明。

1.  **目标：** 我们要证明存在这样两个项，它们是不可证等价的。一个很好的候选是 `T` 和 `(Quote F)`。我们将证明 $\nvdash T \equiv (Quote \ F)$。

2.  **反证法假设：** 假设 STL 是**不一致的**。那么根据定义，对于任意的项 $A, B$，都有 $\vdash A \equiv B$。特别地，我们可以选择 $A=T$ 和 $B=(Quote \ F)$，从而得到：
    $$
    \vdash T \equiv (Quote \ F)
    $$

3.  **应用可靠性定理：** 我们已经证明了 STL 是可靠的。这意味着，如果一个判断是可证的，那么它在我们的模型中必须是有效的。因此，从上面的假设可以推断出：
    $$
    T \models (Quote \ F)
    $$

4.  **在模型中检验：** 根据我们模型的定义，$T \models (Quote \ F)$ 意味着：
    $$
    \text{eval}(T) = \text{eval}((Quote \ F))
    $$

5.  **计算范式：**
    *   `eval(T)`: `T` 是一个原子，没有任何化简规则适用于它。所以 $\text{eval}(T) = T$。
    *   `eval((Quote F))`: `F` 是原子，`eval(F)=F`。`Quote` 是原子，`eval(Quote)=Quote`。组合起来的 `(Quote F)` 不匹配任何化简规则的左侧。所以 $\text{eval}((Quote \ F)) = (Quote \ F)$。

6.  **得出矛盾：** 将计算结果代入第 4 步的等式，我们得到：
    $$
    T = (Quote \ F)
    $$
    这个等式声称原子项 `T` 与列表项 `(Quote F)` 在语法上是完全相同的。这显然是**错误**的。

7.  **结论：** 我们的反证法假设（即“STL是不一致的”）导致了一个逻辑矛盾。因此，这个假设必须是错误的。

所以，STL 系统是**一致的**。具体来说，我们已经证明了 `T ≡ (Quote F)` 在 STL 中是不可证明的。