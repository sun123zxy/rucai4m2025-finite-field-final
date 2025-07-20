import Mathlib

/-!
Exercise 3.30: Show that ∑_{d ∣ n} φ(d) / d = φ(n) / n.

We apply the notion of Dirichlet convolution to simplify this formula to μ * id = φ.
This is by the fact that
φ = φ * I * μ = id * μ

The Euler's totient function φ is implemented in `Nat`, so we pack it into an
`ArithmeticFunction`, where Mathlib have implemented Dirichlet convolution for us.
We also need to translate the `Nat` version of identity φ * I = 1 into that of
`ArithmeticFunction`.
-/

open ArithmeticFunction

/-- Coercion of Euler's totient function from `Nat` to `ArithmeticFunction ℕ`.
    This allows us to use the totient function with Dirichlet convolution operations. -/
def totient : ArithmeticFunction ℕ :=
  ⟨fun n => n.totient, by simp only [Nat.totient_zero]⟩

notation "φ" => totient

/-- The coerced totient function applied to `n` equals `n.totient`. -/
@[simp] lemma coe_totient_apply (n : ℕ) : φ n = n.totient := rfl

/-- φ * ζ = id. This is the arithmetic function version of the classical identity
    ∑_{d ∣ n} φ(d) = n. -/
theorem coe_totient_mul_coe_zeta : φ * ζ = (id : ArithmeticFunction ℕ) := by
  ext n
  simp only [mul_apply, zeta_apply, mul_ite, mul_zero, mul_one, id_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun x y ↦ if y = 0 then 0 else φ x) (n := n)]
  conv => rhs; rw [←Nat.sum_totient n]; rhs; change φ
  rw [Finset.sum_congr rfl]
  intro x hx
  simp only [Nat.div_eq_zero_iff, ite_eq_right_iff]
  rintro (h | h)
  · simp [h]
  · linarith [Nat.divisor_le hx]

/-- μ * id = φ in the notion of arithmetic function. -/
theorem moebius_mul_id : μ * (id : ArithmeticFunction ℕ) = φ := by
  rw [← coe_totient_mul_coe_zeta]
  push_cast
  rw [mul_comm, mul_assoc]
  conv => enter [1,2]; rw [mul_comm]
  rw [moebius_mul_coe_zeta, mul_one]
