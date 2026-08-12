import GaloisForLFunctions.RHTower.DeningerMobiusPrimeNormalSuccessorBlowup

/-!
# The scalar shadow of the Möbius successor blow-up

Fourier--Laplace transformation turns the source successor transport into an identity of
prime-normal Dirichlet amplitudes

`(r/p)^{ms} (M_{p,m}(s) - μ(p)) = M_{r,m}(s)`,

on the honest convergence half-plane `1 < Re(ms)`.  The proof is the same as on the source side:
the head term of `M_{p,m}` is exactly `μ(p)`, and every index strictly between `p` and its Möbius
successor carries a vanishing coefficient.

* `mobiusThetaPrimeNormalAmplitude` : `M_{p,m}(s)`.
* `mobiusThetaPrimeNormalAmplitude_successor` : **the scalar successor identity.**
-/

namespace RHTower

open scoped ArithmeticFunction LSeries.notation

noncomputable section

/-- The prime-normal Dirichlet amplitude `M_{p,m}(s) = ∑_{n ≥ p} μ(n)(p/n)^{ms}`. -/
def mobiusThetaPrimeNormalAmplitude (p m : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ ((m : ℂ) * s)
    * ∑' n : ℕ, if p ≤ n then LSeries.term (↗ArithmeticFunction.moebius) ((m : ℂ) * s) n else 0

theorem lSeriesSummable_moebius_of_one_lt_re {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (↗ArithmeticFunction.moebius) z := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) hz
  have h := ArithmeticFunction.abs_moebius_le_one (n := n)
  have hcast : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖
      = |(ArithmeticFunction.moebius n : ℤ)| := by
    rw [Complex.norm_intCast]
    push_cast
    rfl
  rw [hcast]
  exact_mod_cast h

/-- The head term of the prime-normal amplitude is exactly `μ(p)`. -/
theorem mobiusThetaPrimeNormalAmplitude_head {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    (p : ℂ) ^ z * LSeries.term (↗ArithmeticFunction.moebius) z p
      = ((ArithmeticFunction.moebius p : ℤ) : ℂ) := by
  have hp0 : p ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hp0]
  have hpow : (p : ℂ) ^ z ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.2 (Or.inl ?_)
    exact_mod_cast Nat.cast_ne_zero.2 hp0
  field_simp

/-- Strictly beyond `p` is the same as at or beyond the Möbius successor. -/
theorem mobiusSuccessor_indicator_eq (p : ℕ) (z : ℂ) :
    (fun n : ℕ => if p < n then LSeries.term (↗ArithmeticFunction.moebius) z n else 0)
      = fun n : ℕ =>
        if mobiusSuccessor p ≤ n then LSeries.term (↗ArithmeticFunction.moebius) z n else 0 := by
  funext n
  by_cases hn : mobiusSuccessor p ≤ n
  · have hpn : p < n := lt_of_lt_of_le (lt_mobiusSuccessor p) hn
    rw [if_pos hpn, if_pos hn]
  · rw [if_neg hn]
    by_cases hpn : p < n
    · rw [if_pos hpn]
      have hzero : ArithmeticFunction.moebius n = 0 :=
        moebius_eq_zero_of_lt_mobiusSuccessor hpn (by omega)
      by_cases hn0 : n = 0
      · rw [hn0, LSeries.term_zero]
      · rw [LSeries.term_of_ne_zero hn0]
        show (((ArithmeticFunction.moebius n : ℤ) : ℂ)) / _ = 0
        rw [hzero]
        simp
    · rw [if_neg hpn]

/-- **The scalar successor identity.**  This is the Fourier--Laplace shadow of the source
transport. -/
theorem mobiusThetaPrimeNormalAmplitude_successor {p m : ℕ} (hp : 1 ≤ p) {s : ℂ}
    (hs : 1 < ((m : ℂ) * s).re) :
    ((mobiusSuccessor p : ℂ) / (p : ℂ)) ^ ((m : ℂ) * s)
        * (mobiusThetaPrimeNormalAmplitude p m s - ((ArithmeticFunction.moebius p : ℤ) : ℂ))
      = mobiusThetaPrimeNormalAmplitude (mobiusSuccessor p) m s := by
  set z : ℂ := (m : ℂ) * s with hzdef
  set t : ℕ → ℂ := LSeries.term (↗ArithmeticFunction.moebius) z with htdef
  have hsum : Summable t := lSeriesSummable_moebius_of_one_lt_re hs
  have hp0 : p ≠ 0 := by omega
  have hr0 : mobiusSuccessor p ≠ 0 := by
    have := mobiusSuccessor_pos hp
    omega
  -- split the head off the amplitude
  have hs1 : Summable fun n : ℕ => if n = p then t n else 0 := by
    refine summable_of_ne_finset_zero (s := {p}) fun n hn => ?_
    rw [if_neg (by simpa using hn)]
  have hs2 : Summable fun n : ℕ => if p < n then t n else 0 := by
    refine Summable.of_norm_bounded hsum.norm fun n => ?_
    by_cases h : p < n <;> simp [h]
  have hsplitfun : (fun n : ℕ => if p ≤ n then t n else 0)
      = (fun n : ℕ => if n = p then t n else 0) + fun n : ℕ => if p < n then t n else 0 := by
    funext n
    simp only [Pi.add_apply]
    rcases lt_trichotomy n p with hlt | heq | hgt
    · rw [if_neg (by omega : ¬ p ≤ n), if_neg (by omega : ¬ n = p),
        if_neg (by omega : ¬ p < n), add_zero]
    · subst heq
      rw [if_pos (le_refl n), if_pos rfl, if_neg (lt_irrefl n), add_zero]
    · rw [if_pos (by omega : p ≤ n), if_neg (by omega : ¬ n = p), if_pos hgt, zero_add]
  have hsplit : (∑' n : ℕ, if p ≤ n then t n else 0)
      = t p + ∑' n : ℕ, if p < n then t n else 0 := by
    rw [hsplitfun]
    show (∑' n : ℕ, ((if n = p then t n else 0) + if p < n then t n else 0)) = _
    rw [hs1.tsum_add hs2, tsum_ite_eq p t]
  -- the amplitude minus its head is the strict tail
  have hhead := mobiusThetaPrimeNormalAmplitude_head hp z
  have hbody : mobiusThetaPrimeNormalAmplitude p m s
      - ((ArithmeticFunction.moebius p : ℤ) : ℂ)
      = (p : ℂ) ^ z * ∑' n : ℕ, if p < n then t n else 0 := by
    rw [mobiusThetaPrimeNormalAmplitude, ← hzdef, ← htdef, hsplit, mul_add, hhead]
    ring
  rw [hbody, mobiusThetaPrimeNormalAmplitude, ← hzdef, ← htdef,
    ← mobiusSuccessor_indicator_eq p z]
  -- combine the two spectral normalizers
  have hprod : ((mobiusSuccessor p : ℂ) / (p : ℂ)) ^ z * (p : ℂ) ^ z
      = (mobiusSuccessor p : ℂ) ^ z := by
    have hpR : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hqR : (0 : ℝ) ≤ (mobiusSuccessor p : ℝ) / (p : ℝ) := by positivity
    have hmul := Complex.mul_cpow_ofReal_nonneg hqR hpR z
    have hpne : ((p : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hp0
    have hL : (((mobiusSuccessor p : ℝ) / (p : ℝ) : ℝ) : ℂ) * (((p : ℕ) : ℝ) : ℂ)
        = ((mobiusSuccessor p : ℕ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      have hreal : ((mobiusSuccessor p : ℝ) / (p : ℝ)) * (p : ℝ)
          = (mobiusSuccessor p : ℝ) := by field_simp
      rw [hreal]
      push_cast
      ring
    have hdiv : ((mobiusSuccessor p : ℂ) / (p : ℂ))
        = (((mobiusSuccessor p : ℝ) / (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have hpcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [hdiv, hpcast, ← hmul, hL]
  calc ((mobiusSuccessor p : ℂ) / (p : ℂ)) ^ z
        * ((p : ℂ) ^ z * ∑' n : ℕ, if p < n then t n else 0)
      = (((mobiusSuccessor p : ℂ) / (p : ℂ)) ^ z * (p : ℂ) ^ z)
        * ∑' n : ℕ, if p < n then t n else 0 := by ring
    _ = (mobiusSuccessor p : ℂ) ^ z * ∑' n : ℕ, if p < n then t n else 0 := by rw [hprod]

end

end RHTower
