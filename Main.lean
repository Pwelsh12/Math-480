import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import LatexInLean
show_panel_widgets [latex]
set_option linter.unusedTactic false

/-
Tactics cheatsheet:
  - `rw [<theorem1>, <theorem2>]` to use theorems of the form `a = b` to rewrite the goal.
  - `calc a = b := by ...
          _ = c := by ...` to prove that `a = c` with intermediate steps in between.
  - `ring` to automatically prove equalities that involve basic algebra simplification without division.
  - `linarith` to automatically prove equality or inequalities that involve addition, subtraction, and multiplication by constants
  - `simp` to automatically prove equalities by reducing both sides to their "simplest" form
  - `rel [<theorem1>, <theorem2>]` to prove `a ≤ c` by using theorems like `a ≤ b` and `b ≤ c`.
  - `exact <theorem>` to finish the proof using theorem.
  - `by_contra <hypothesis>` convert the proof to a contradiction proof and insert the negation of the conclusion as a hypothesis.
  - `done` is a placeholder tactic you can use at the end of a proof to indicate all goals are solved.
-/

/-
  Logical connectives:
  - Iff is ↔ and you use `apply Iff.intro` in order to split the goal into two cases, the forward direction (`mp` for `modus ponens`) and the backwards direction (`mpr` for `modus ponens reverse`).
  - To prove that `p → q`, use `intro h` to make `p` a hypothesis and then prove `q` from there.
-/

/-
  Searching mathlib cheatsheet:
  - `add`, `sub`, `mul`, `div` for +, -, *, /
  - `lt`, `le`, `gt`, `ge`, `eq`, `ne` for <, ≤, >, ≥, =, ≠
  - `assoc` and `comm` for associativity and commutativity
-/

theorem linear_formula (a : ℝ) (b: ℝ) (x: ℝ) (ha_ne_zero : a ≠ 0) : a*x+b = 0 ↔ x = -b/a := by
  apply Iff.intro
  case mp =>
    intro h
    have h_ax : x * a = -b := by linarith
    exact (eq_div_of_mul_eq ha_ne_zero h_ax)



  case mpr =>
    intro h
    calc a * x + b = a * (-b/a) + b := by rw [h]
                  _= -b * (a/a) + b := by ring
                  _= -b * 1 + b := by simp [ha_ne_zero]
                  _= -b + b := by ring
                  _= 0 := by ring
