import Mathlib
/-
Every element of a finite field F of order q is the kth power of some element of F_q
if and only if k.gcd (q - 1) = 1.
-/
theorem surjective_of_pow_iff_coprime {K : Type*} [Field K] [Fintype K] [DecidableEq K] (k : ℕ) (zk : k ≠ 0) : Function.Surjective (fun (a : K) => a ^ k) ↔ k.gcd (Fintype.card K - 1) = 1 := by
  rw [← Finite.injective_iff_surjective_of_equiv (by rfl), ← (Fintype.card_units K)]
  simp [Function.Injective]  --transform to injectivity
  have h1 : ∀ a : Kˣ, a ^ (Fintype.card Kˣ) = 1 := by exact fun a => pow_card_eq_one
  constructor
  · intro h
    have h2 : ∀ (a₁ a₂ : Kˣ), a₁ ^ k = a₂ ^ k → a₁ = a₂ := by
      intro a₁ a₂ heq
      apply Units.ext
      exact @h ↑a₁ ↑a₂ (by rw [← Units.val_pow_eq_pow_val,← Units.val_pow_eq_pow_val, heq])
    contrapose! h2
    use 1
    simp
    set t := Fintype.card Kˣ / k.gcd (Fintype.card Kˣ) with ht
    have h3 : ∃ a : Kˣ,  a ^ t ≠ 1 := by
      refine exists_pow_ne_one_of_isCyclic ?_ ?_
      · rw [ht]
        refine (Nat.div_ne_zero_iff_of_dvd (Nat.gcd_dvd_right _ _)).mpr ?_
        constructor
        · exact Fintype.card_ne_zero
        exact Nat.gcd_ne_zero_left zk
      rw [Nat.card_eq_fintype_card, ht]
      refine Nat.div_lt_self ?_ ?_
      · exact Fintype.card_pos
      have : k.gcd (Fintype.card Kˣ) ≠ 0 := by exact Nat.gcd_ne_zero_left zk
      omega
    rcases h3 with ⟨a, ha⟩
    use a ^ t
    constructor
    · rw [← pow_mul]
      simp [t]
      rw [mul_comm,← Nat.mul_div_assoc, mul_comm, Nat.mul_div_assoc, pow_mul, h1]
      simp
      exact Nat.gcd_dvd_left k (Fintype.card Kˣ)
      exact Nat.gcd_dvd_right k (Fintype.card Kˣ)
    intro v
    exact ha (Eq.symm v)
  -- Similarly transform to the cyclic group Fˣ.
  intro h a₁ a₂ hk
  have bezout : ∃ s t : ℤ , 1 = k * s + Fintype.card Kˣ * t := by
    rw [← Int.ofNat_one, ← h]
    apply Int.gcd_dvd_iff.1
    simp
  rcases bezout with ⟨s, t, bst⟩
  by_cases z : a₁ = 0
  · rw [z, zero_pow zk] at hk
    rw [z]
    by_cases z2 : a₂ = 0
    · rw [z2]
    exfalso
    exact pow_ne_zero k z2 (Eq.symm hk)
  by_cases z2 : a₂ = 0
  · rw [z2, zero_pow zk] at hk
    exfalso
    exact pow_ne_zero k z hk
  set c : Kˣ := ⟨a₁ * a₂⁻¹, a₂ * a₁⁻¹, by field_simp [z, z2], by field_simp [z, z2]⟩
  rw [← mul_inv_eq_one₀]
  rw [← mul_inv_eq_one₀, ← inv_pow, ← mul_pow] at hk
  · have hc : c.val = a₁ * a₂⁻¹ := by rfl
    have v1 : ↑(1 : Kˣ) = (1 : K) := by rfl
    rw [← hc, ← v1]
    rw [← hc, ← v1] at hk
    norm_cast at hk
    norm_cast
    rw [← zpow_one c, bst, zpow_add, zpow_mul, zpow_mul]
    norm_cast
    rw [hk, h1 c]
    simp
  intro hk2
  rw [hk2] at hk
  exact pow_ne_zero k z hk
  exact z2
