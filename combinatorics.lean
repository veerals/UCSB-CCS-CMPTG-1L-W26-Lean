-- Proof n choose k equals n choose n-k.

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring.Basic
theorem Choose_Symmetry (n k : ℕ) (h : k ≤ n) : Nat.choose n k = Nat.choose n (n - k) := by
  rw [Nat.choose_eq_factorial_div_factorial h]
  rw [Nat.choose_eq_factorial_div_factorial (Nat.sub_le n k)]
  rw [mul_comm (Nat.factorial k) (Nat.factorial (n - k))]
  rw [Nat.sub_sub_self h]


theorem pascal_identity (n k : ℕ) (h : k ≤ n) (h' : k ≤ n-1) (h'' : 1 ≤ k) :
    Nat.choose n k = Nat.choose (n-1) (k-1) + Nat.choose (n-1) (k) := by
  --have h₂ : k ≤ n := Nat.le_add_left 1 h
  --rw[Nat.choose_eq_factorial_div_factorial h₁]
  --rw[Nat.choose_eq_factorial_div_factorial h₂]
  --rw[Nat.choose_eq_factorial_div_factorial h]
  --rw[Nat.add_sub_add_right_eq_sub]
  --rw[succ_sub_succ_eq_sub]
  --rw[factorial_succ]
  --rw[mul_comm]
  --rw[mul_left_comm]
  --rw[mul_assoc]
  rw[Nat.choose_eq_factorial_div_factorial h]
  rw [Nat.choose_eq_factorial_div_factorial h']

  have h_1 : k-1 ≤ n-1 := by
    have thing :=  Nat.pred_le k
    have thing' := Nat.le_trans thing h'
    exact thing'

  have n_lower_bound : 1 ≤ n := by
    sorry

  rw [Nat.choose_eq_factorial_div_factorial h_1]
  set val1 := (n-1).factorial / (k.factorial * (n-k).factorial)
  have hval1 : val1 = (n-1).factorial / (k.factorial * (n-k).factorial) := by rfl
  have val2  : k ≠ 0 := by
    sorry

  have h4 : n - 1 + 1 = n := by
    rw [Nat.sub_add_cancel n_lower_bound]

 -- turn into proper n-k factorial instead of what it is now.
  have h_2 : (n - 1 - (k - 1)).factorial = (n - k).factorial := by
    apply congr_arg Nat.factorial
    rw [Nat.sub_sub]
    conv =>
      lhs
      rhs
      rw [add_comm]
    rw [Nat.sub_add_cancel h'']


  conv =>
    rhs
    lhs
    rhs
    rhs
    rw [h_2]

  -- convert to n-1+1 factorial so we can use the factorial_succ
  conv =>
    lhs
    lhs
    apply congr_arg Nat.factorial
    rw [← h4]

  rw [Nat.factorial_succ]

  have hLHS1 : (n - 1 + 1) = n := by
    rw [Nat.sub_add_cancel n_lower_bound]
  rw [hLHS1]


  have hLHS : n * (n - 1).factorial / (k.factorial * (n - k).factorial) = n * val1 := by
    sorry

  rw [hLHS]

  have hRHS1 : (n-1).factorial / ((k-1).factorial * (n-k).factorial) = val1 * k := by
    sorry
  rw [hRHS1]

  have hRHS2 : (n-1).factorial / (k.factorial * (n-1-k).factorial) = val1 * (n-k) := by
    sorry
  rw [hRHS2]
  conv =>
    lhs
    rw [mul_comm]
  
  conv =>
    rhs
    rw [← mul_add]
    rhs
    rw [Nat.add_sub_cancel' h]
