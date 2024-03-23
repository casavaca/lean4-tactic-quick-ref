# Lean 4 tactics — quick ref

<details><summary> apply </summary>
</details>

<details><summary> assumption </summary>
+ close the goal with a hypothesis, or fail.
+ included by `trivial`
</details>

<details><summary> cases / cases' </summary>
TODO
</details>

<details><summary> clear </summary>
removes the given hypotheses, or fails if there are remaining references to a hypothesis
</details>

<details><summary> constructor </summary>
If the main goal's target type is an inductive type, `constructor` solves it with
the first matching constructor, or else fails.
</details>

<details><summary> contradiction </summary>
+ closes the main goal if its hypotheses are "trivially contradictory".
+ included by `trivial`
</details>

<details><summary> exfalso </summary>
turn the goal into False
</details>

<details><summary> exact / refine / refine' </summary>
+ `exact e` : close the goal using `e`
+ refine is similar to exact, but allow holes, which are turned into new goals.
e.g., `refine succ_lt_succ (Nat.lt_trans ?_ (lt_succ_self _))`
+ refine' is similar to refine, but unsolved `_` and implicit parameters are also turned into new goals.
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

<details><summary> infer_instance </summary>
`exact inferInstance`
</details>

<details><summary> **let / set** </summary>
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
</details>

<details><summary> **linarith** </summary>
linear (in)equalities over ℕ, ℤ, and ℚ
</details>

<details><summary> obtain </summary>
example {a b : Nat} (h : a ≤ b ∧ b ≤ a) : a = b := by
  obtain ⟨h1, h2⟩ := h
  exact Nat.eq_of_le_of_lt_succ h2 $ Nat.lt_succ_of_le h1
</details>

<details><summary> **omega** </summary>
solve integer / natural number linear problems
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

<details><summary> rfl / rfl' / ac_rfl </summary>
+ `rfl`    : trying to close the goal by reflexivity. included by `trivial`
+ `rfl'`   : `set_option smartUnfolding false in with_unfolding_all rfl`
+ `ac_rfl` : `example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by ac_rfl`
</details>

<details><summary> rw </summary>
```lean
example (n : ℕ) (h : n = 2 + 2) : n = 4 := by
  -- ⊢ n = 4
  rw [(by rfl : 4 = 2 + 2)]
  -- ⊢ n = 2 + 2
```
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
repeat ...                            :
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
