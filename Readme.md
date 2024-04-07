# Lean 4 tactics — quick ref

<details><summary> apply </summary>

  Roughly, if goal is T, and H is A -> B -> T,
  `apply H` is like
  exact (H ?_ ?_) where ?_ means now goals generated.
</details>

<details><summary> apply_fun </summary>

  -- h : a = b
  apply_fun f at h
  -- h : f a = f b
</details>

<details><summary> assumption </summary>

  + close the goal with a hypothesis, or fail.
  + included by `trivial`
</details>

<details><summary> by_cases / cases / cases' / <b>rcases</b> </summary>

  TODO
</details>

<details><summary> calc </summary>

  Proof by calculation. Also works for inequality.
  ```lean
  calc
    blah = blah1  := by ...
    _    = blah2  := by ...
    _    = blah3  := by ...
    _    = target := by ...
  ```
</details>

<details><summary> clear </summary>

  removes the given hypotheses, or fails if there are remaining references to a hypothesis
</details>

<details><summary> congr / <b>gcongr</b> </summary>

  + congr:
    For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
    `congr` produces the goals `⊢ x = y` and `⊢ y = x`,
    while `congr 2` produces the intended `⊢ x + y = y + x`.
  + <b>gcongr</b>:
    generalized congr. also work for inequality

    trace: `set_option trace.Meta.gcongr true in`
</details>

<details><summary> constructor </summary>

  If the main goal's target type is an inductive type, `constructor` solves it with the first matching constructor, or else fails.
</details>

<details><summary> contrapose / contrapose! </summary>

  * `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
  * `contrapose!`    turns a goal `P → Q` into `¬ Q → ¬ P` and pushes negations inside `P` and `Q` using `push_neg`
  * `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
  * `contrapose! h`  first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`
  * `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis
</details>

<details><summary> contradiction </summary>

  + closes the main goal if its hypotheses are "trivially contradictory".
  + included by `trivial`
</details>

<details><summary> <b>convert</b> / <b>convert_to</b> </summary>

  ```lean
  h : 2 * (a * b + b * c + c * a) ≥ a ^ 2 + b ^ 2 + c ^ 2
  ⊢   2 * (b * a + a * c + c * b) ≥ b ^ 2 + a ^ 2 + c ^ 2

  convert h using 1
  ⊢   2 * (b * a + a * c + c * b) = 2 * (a * b + b * c + c * a)
  ⊢   b ^ 2 + a ^ 2 + c ^ 2 = a ^ 2 + b ^ 2 + c ^ 2

  convert h using 2 -- Note that this is too much
  ⊢   2 = 2          -- solved by the tactic
  ⊢   (b * a + a * c + c * b) = (a * b + b * c + c * a)
  ⊢   b ^ 2 = a ^ 2
  ⊢   a ^ 2 = b ^ 2
  ⊢   c ^ 2 = c ^ 2 -- solved

  h : 2 * (a * b + b * c + c * a) ≥ a ^ 2 + b ^ 2 + c ^ 2
  ⊢   2 * (b * a + a * c + c * b) ≥ b ^ 2 + a ^ 2 + c ^ 2
  move_add [←(a^2)] -- move a^2 to the left
  h : 2 * (a * b + b * c + c * a) ≥ a ^ 2 + b ^ 2 + c ^ 2
  ⊢   2 * (b * a + a * c + c * b) ≥ a ^ 2 + b ^ 2 + c ^ 2
  convert h using 2
  ⊢   (b * a + a * c + c * b) = (a * b + b * c + c * a)
  ring_nf
  ```

  `convert_to g = convert (?_ : g)`

  ```lean
  ⊢ a > b
  convert_to (c > d)
  ⊢ c > d
  ⊢ a = c
  ⊢ b = d
  ```
</details>

<details><summary> delta </summary>

  `delta id1 id2 ...` delta-expands the definitions `id1`, `id2`, ....

  This is a low-level tactic, it will expose how recursive definitions have been compiled by Lean.
</details>

<details><summary> exists </summary>

  `exists e₁, e₂, ...` is shorthand for `refine ⟨e₁, e₂, ...⟩; try trivial`.
</details>

<details><summary> exfalso </summary>

  turn the goal into False
</details>

<details><summary> exact / refine / refine' </summary>

  + `exact e` : close the goal using `e`
  + `refine` is similar to exact, but allow holes, which are turned into new goals.
  + e.g., `refine succ_lt_succ (Nat.lt_trans ?_ (lt_succ_self _))`
  + `refine'` is similar to refine, but unsolved `_` and implicit parameters are also turned into new goals.
</details>

<details><summary> <b>fin_cases</b> </summary>

  + e.g.: Convert `Fin 3` into `0, 1, 2`
</details>
<details><summary> generalize </summary>

  ```lean
  example : 2 + 3 = 5 := by
    -- Goals (1)
    -- ⊢ 2 + 3 = 5
    generalize h : 3 = x
    -- Goals (1)
    -- x : ℕ
    -- h : 3 = x
    -- ⊢ 2 + x = 5
    rw [← h]
  ```
</details>

<details><summary> have / have' </summary>

  + have: TODO
  + have': similar to refine'
</details>

<details><summary> induction </summary>

</details>

<details><summary> <b>induction'</b> </summary>

  + induction on list length: `induction' ih : l.length generalizing l`
  + strong induction on list length: `induction' ih : l.length using Nat.case_strong_induction_on generalizing l`
</details>

<details><summary> infer_instance </summary>

  `exact inferInstance`
</details>

<details><summary> injection / injections </summary>

  + injection : from `(a::b) = (c::d)` we derive `a=c` and `b=d`.
  + injections: do it recursively.
</details>

<details><summary> let / set / let' </summary>

  ```lean
  example : 2 + 3 = 5 := by
    -- Goals (1)
    -- ⊢ 2 + 3 = 5
    set x := 3 with h
    -- Goals (1)
    -- x : ℕ := 3
    -- h : x = 3
    -- ⊢ 2 + x = 5
  ```

  + let': similar to refine'
</details>

<details><summary> <b>linarith</b> <b>nlinarith</b> </summary>

  linear (in)equalities over ℕ, ℤ, and ℚ

  nlinarith is more powerful. Try it when you think linarith should work but it didn't.
</details>

<details><summary> <b>linear_combination </b> </summary>

  Let's say we have `h₁ : 2 * a + b = c` and want to proof `a = (c - b) / 2`. We would like lean to do the transposition, but lean is not that smart. `linear_combination` allow us to do the following:
  `a - (c - b) / 2 - (1/2) * (2 * a + b - c) = 0 → a = (c - b) / 2`

  Basically, it is `lhs - rhs - n₁ * (h₁.left - h₁.right) - n₂ * (h₂.left - h₂.right) - ... → lhs = rhs`.

  You need to feed the coefficient manually.

  Sometimes lean can't figure out if denom ≠ 0, use `linear_combination (norm := (field_simp; ring)) h * ...`

  If lean still can't figure out, help it by doing `have : denom ≠ 0 := by your_proof`

  Sometimes, it still won't work because ↑(m / n) = ↑m / ↑n isn't always true. You need to help lean again:

  ```lean
  example (k a b : ℤ) (ha : 1 < a) (hb : 1 < b)
    (h : k * (a - 1) * (b - 1) = a * b) : k = (a * b) / ((a - 1) * (b - 1)) := by
    have hh : ((a - 1) * (b - 1) ∣ (a * b)) := by apply dvd_of_mul_left_eq k; rw [←h]; ring
    have : a ≠ 0 := by apply ne_of_gt; trans 1; simp; assumption
    have : b ≠ 0 := by apply ne_of_gt; trans 1; simp; assumption
    have : a - 1 ≠ 0 := by apply ne_of_gt; simpa
    have : b - 1 ≠ 0 := by apply ne_of_gt; simpa
    qify at *
    -- ⊢ ↑k = ↑(a * b / ((a - 1) * (b - 1)))
    rw [(Rat.coe_int_div _ _ hh)]
    push_cast
    -- ⊢ ↑k = ↑a * ↑b / ((↑a - 1) * (↑b - 1))
    linear_combination (norm := (field_simp; ring)) h * (1 / (a - 1) / (b - 1))
  ```
</details>

<details><summary> match </summary>

  ```lean
  have : m < 4 := by ...
  match h : m with
  | 0 => sorry
  | 1 => sorry
  | 2 => sorry
  | 3 => sorry
  | h + 4 => contradiction
  ```
</details>

<details><summary> <b>move_add, move_mul</b> </summary>

  rearrange of `a + b + c + d + ...`
  e.g., `move_add [a, b, c, ← d, ← e]` returns `d + e + [...] + a + b + c`
</details>

<details><summary> norm_cast / push_cast </summary>

</details>

<details><summary> obtain </summary>

   ```lean
   example {a b : Nat} (h : a ≤ b ∧ b ≤ a) : a = b := by
     obtain ⟨h1, h2⟩ := h
     exact Nat.eq_of_le_of_lt_succ h2 $ Nat.lt_succ_of_le h1
  ```
</details>

<details><summary> omega / bv_omega </summary>

  + omega: solve integer / natural number linear problems
  + bv_omega: additional helper with BitVec
</details>

<details><summary> rename / rename_i </summary>

  ```lean
  example : ∀ e a b c d : Nat, a = b → a = d → a = c → c = b := by
    intros
    -- Goals (1)
    -- e a³ b c d : ℕ
    -- a² : a³ = b
    -- a¹ : a³ = d
    -- a : a³ = c
    -- ⊢ c = b
    rename _ = _ => hac -- rename last type of _ = _ to hac
    rename_i hab _      -- rename last unnamed hypothesis with _, second last with hab
    -- Goals (1)
    -- e a¹ b c d : ℕ
    -- hab : a¹ = b
    -- a : a¹ = d
    -- hac : a¹ = c
    -- ⊢ c = b
    apply Eq.trans
    apply Eq.symm
    exact hac
    exact hab
  ```
</details>


<details><summary> revert </summary>

  move the hypothesis into goal.
</details>

<details><summary> rewrite / rw </summary>

  ```lean
  example (n : ℕ) (h : n = 2 + 2) : n = 4 := by
    -- ⊢ n = 4
    rw [(by rfl : 4 = 2 + 2)]
    -- ⊢ n = 2 + 2
  ```
</details>

<details><summary> simp / simp_all / dsimp / simpa </summary>

  + simp
  + simp_all : stronger `simp [*] at *`
  + dsimp: definitional simp
  + simpa: closing form. `simpa [...]` or `simpa [...] using e`.
</details>

<details><summary> specialize </summary>

</details>

<details><summary> split </summary>

</details>

<details><summary> suffices </summary>

  TODO
</details>

<details><summary> symm </summary>

  convert `a = b` to `b = a`.
</details>


<details><summary> rfl / rfl' / ac_rfl </summary>

  + `rfl`    : trying to close the goal by reflexivity. included by `trivial`
  + `rfl'`   : `set_option smartUnfolding false in with_unfolding_all rfl`
  + `ac_rfl` : `example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by ac_rfl`
</details>

<details><summary> tauto </summary>

  Solve first order logic problems. e.g.:

  `a → ((b ∧ c) ↔ (a ∧ b ∧ c))`
</details>
<details><summary> <b>trans</b> </summary>

  turn `a = b` into `a = ?` and `? = b`
</details>

<details><summary> unfold </summary>

  + `unfold id` unfolds definition `id`.
  + `unfold id1 id2 ...` is equivalent to `unfold id1; unfold id2; ...`.
</details>

## Mathematics

<details><summary> <b>abel</b> </summary>

</details>

<details><summary> <b>field_simp</b> </summary>

  TODO.

  ```lean
  -- this : k - 1 > 0
  -- ⊢ (k - 1) * (k / (k - 1)) < ...
  field_simp -- doesn't work.
  -- ⊢ k < ...
  field_simp [mul_comm] -- works.


</details>

<details><summary> <b>ring / ring!</b> </summary>

</details>

## Tactic meta / debug / trace

+ `with_reducible` / `with_reducible_and_instances`
   only definitions tagged with `@[reducible]` are unfolded

+ `with_unfolding_all`
   all definitions (except opaque ones) are unfolded

## Tactic Combinators / Reorder goals.

```
tac1 <;> ta2                          : tag2 on each produced goal of tac1

skip                                  : do nothing and succeed.
done                                  : succeeds iff there are no remaining goals.
next                                  : focus on the next goal
focus                                 : focus on main goal and suppress other goals.
first | apply xyz | assumption | ...  : try these in order until one succeeds.
try ...                               : same as `first ... | skip`
repeat / repeat' / repeate1'          :
all_goals ...                         :
any_goals ...                         :
pick_goal n                           : move `n`-th goal to the front
pick_goal -n                          : move `n`-th goal (counting backwards) to the front
on_goal n                             : create a block scope for `n`-th goal
on_goal -n                            : create a block scope for `-n`-th goal
rotate_left n                         : imagine all goals as a list, rotate left the goals.
rotate_right n                        : imagine all goals as a list, rotate left the goals.
swap                                  : `pick_goal 2`
```
