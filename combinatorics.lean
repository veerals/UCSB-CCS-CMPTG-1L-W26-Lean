-- Proof n choose k equals n choose n-k.

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring

theorem Choose_Symmetry (n k : ℕ) (h : k ≤ n) : Nat.choose n k = Nat.choose n (n - k) := by
  rw [Nat.choose_eq_factorial_div_factorial h]
  rw [Nat.choose_eq_factorial_div_factorial (Nat.sub_le n k)]
  rw [Nat.sub_sub_self]
  rw [mul_comm (n-k).factorial k.factorial ]
  apply h

theorem pascal_identity (n k : ℕ) (h : k ≤ n)(h'' : 1 ≤ k) :
    Nat.choose n k = Nat.choose (n-1) (k-1) + Nat.choose (n-1) (k) := by

  have h_1 : k-1 ≤ n-1 := Nat.sub_le_sub_right h 1

  have n_lower_bound : 1 ≤ n := by
    exact le_trans h'' h

  have n_lower_bound_minus : 0 ≤ n - 1 := Nat.zero_le (n - 1)

  have n_lower_bound' : 0 < n := n_lower_bound

  have n_neq_0 : n ≠ 0 := by
    exact ne_of_gt n_lower_bound


  have h4 : n - 1 + 1 = n := by
    rw [Nat.sub_add_cancel n_lower_bound]

  rw [Nat.choose_eq_factorial_div_factorial h_1]

  cases lt_or_eq_of_le h with
    | inl hlt =>
    -- k < n
      have h' : k ≤ n-1 := Nat.le_pred_of_lt hlt
      rw[Nat.choose_eq_factorial_div_factorial h]
      rw [Nat.choose_eq_factorial_div_factorial h']

      set val1 := (n-1).factorial / (k.factorial * (n-k).factorial)
      have hval1 : val1 = (n-1).factorial / (k.factorial * (n-k).factorial) := by rfl
      have h14 : 0 < n-k := Nat.sub_pos_of_lt hlt



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

      have h4 : n - 1 + 1 = n := by
        rw [Nat.sub_add_cancel n_lower_bound]

      conv =>
        lhs
        lhs
        apply congr_arg Nat.factorial
        rw [← h4]

      rw [Nat.factorial_succ]

      have hLHS1 : (n - 1 + 1) = n := by
        rw [Nat.sub_add_cancel n_lower_bound]
      rw [hLHS1]


      have hfact : n * (n - 1).factorial = n.factorial := by
        rw [Nat.mul_factorial_pred n_neq_0]

      have h_main : n * (n - 1).factorial / (k.factorial * (n - k).factorial) =
        (n - 1).factorial / ((k - 1).factorial * (n - k).factorial) +
        (n - 1).factorial / (k.factorial * (n - 1 - k).factorial) := by

        have h5 : n-k-1+1 = n-k := by
          exact Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h14)

        have h6 : n-k ≠ 0 := by
          have hpos : 0 < n - k := Nat.sub_pos_of_lt hlt
          exact ne_of_gt hpos

        have h1 : (n-1).factorial / ((k-1).factorial * (n-k).factorial)
          = k * ((n-1).factorial / (k.factorial * (n-k).factorial)) := by
          obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' h''
          rw [Nat.factorial_succ]
          rw [show (l+1) * l.factorial * (n-(l+1)).factorial
            = l.factorial * (n-(l+1)).factorial * (l+1) by ring]
          rw [Nat.add_sub_cancel]
          conv_rhs =>
            rw [mul_comm (l+1) _]
          rw [Nat.mul_comm (l.factorial * (n-(l+1)).factorial) (l+1)]
          rw [← Nat.mul_assoc]
          rw [show (l+1) * l.factorial * (n-(l+1)).factorial
          = l.factorial * (n-(l+1)).factorial * (l+1) by ring]
          have h8 : n - (l + 1) = n - 1-l := by
            conv =>
              lhs
              rw [add_comm]
            rw [Nat.sub_sub]
          rw [h8]
          rw [← Nat.choose_eq_factorial_div_factorial (by omega : l ≤ n-1)]
          rw [show l.factorial * (n-1-l).factorial * (l+1)
            = (l.factorial * (n-1-l).factorial) * (l+1) by ring]
          rw [← Nat.div_div_eq_div_mul]
          rw [← Nat.choose_eq_factorial_div_factorial (by omega : l ≤ n-1)]
          apply (Nat.div_mul_cancel _).symm


        have h2 : (n-1).factorial / (k.factorial * (n-1-k).factorial)
          = (n-k) * ((n-1).factorial / (k.factorial * (n-k).factorial)) := by
          have hpos : 0 < n - k := Nat.sub_pos_of_lt hlt
          have hnk : (n-k).factorial = (n-k) * (n-k-1).factorial := by
            conv_lhs =>
              rw [← h5]
            rw [Nat.factorial_succ]
            rw [h5]
          have hstep : n - 1 - k = n - k - 1 := by omega
          have hdvd : k.factorial * (n-k-1).factorial ∣ (n-1).factorial := by
            rw [show n - k - 1 = n - 1 - k by omega]
            exact Nat.factorial_mul_factorial_dvd_factorial h'
          rw [hstep]
          rw [show k.factorial * (n-k).factorial
              = k.factorial * (n-k-1).factorial * (n-k) by rw [hnk]; ring]
          symm
          rw [Nat.mul_comm (n-k) _]
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.div_mul_cancel]
          have h7 : n-1-k = n-k-1 := by omega
          conv =>
            rhs
            rw [← h7]

          rw [← Nat.choose_eq_factorial_div_factorial h']
        rw [h1, h2]

        have h3 :
          k * ((n - 1).factorial / (k.factorial * (n - k).factorial)) +
          (n - k) * ((n - 1).factorial / (k.factorial * (n - k).factorial))
            =
          (k + (n - k)) * ((n - 1).factorial / (k.factorial * (n - k).factorial)) := by
          rw [← Nat.add_mul]



        rw [h3]
        rw [Nat.add_sub_cancel' h]
        rw [Nat.mul_comm]
        rw [mul_comm ((n-1).factorial) n, Nat.mul_div_assoc] 


      rw [h_main]

/-
      have hLHS :
        n * (n - 1).factorial / (k.factorial * (n - k).factorial) = n * val1 := by
        rw [hfact]        -- turns numerator into n.factorial
        rw [hval1]
        symm
        have hdvd : k.factorial * (n - k).factorial ∣ n.factorial := by
          exact Nat.factorial_mul_factorial_dvd_factorial h
        exact Nat.mul_div_assoc n hdvd



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
-/
    | inr heq =>
      -- k = n (n-1 choose k = 0)
      have h'''' : 0 < (n-1).factorial := by
        exact Nat.factorial_pos (n-1)
      rw [heq]
      rw [Nat.choose_self n]
      rw [Nat.choose_eq_zero_of_lt]
      rw [Nat.add_zero]
      conv =>
        rhs
        rw [Nat.sub_self]
        rw [Nat.factorial]
        rw [Nat.mul_one]
        rw [Nat.div_self h'''']
      exact Nat.sub_lt n_lower_bound' Nat.one_pos


theorem pascal_identity1 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Nat.choose n k = Nat.choose (n-1) (k-1) + Nat.choose (n-1) k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_of_le' hn
  rfl
