import GaloisForLFunctions.HTGeometry.FaceShiftLatticeNonresonance

/-!
# Integrally independent periods in the upper half plane

The external face lattice of the elliptic gamma hierarchy is nonresonant under
`PeriodsIntegrallyIndependent` — no integral relation holds between `1` and the periods — but the
hypothesis has no realization, so every statement about the bottom layer is conditional.  It is in
fact elementary: purely imaginary periods make the coefficient of `1` the real part, and unique
factorization separates the imaginary parts when they are logarithms of distinct primes.

* `logPrimePeriod`, `logPrimePeriod_im_pos`;
* **`periodsIntegrallyIndependent_logPrimePeriod`**, **`exists_periods_im_pos_integrallyIndependent`**
  — a period family in the upper half plane with no integral relation, over any finite index;
* **`linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent`** — the connector
  to the rank-three source hypothesis of the elliptic gamma packet, which is the pair restriction of
  the lattice hypothesis;
* `linearIndependent_ellipticGammaSourcePeriods_logPrime` — that hypothesis on explicit periods.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type} [Fintype ι]

/-- The purely imaginary period family attached to a family of primes. -/
noncomputable def logPrimePeriod (q : ι → Nat.Primes) : ι → ℂ :=
  fun i => Complex.I * (Real.log (q i : ℕ) : ℂ)

omit [Fintype ι] in
@[simp] theorem logPrimePeriod_re (q : ι → Nat.Primes) (i : ι) :
    (logPrimePeriod q i).re = 0 := by
  unfold logPrimePeriod
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [Fintype ι] in
@[simp] theorem logPrimePeriod_im (q : ι → Nat.Primes) (i : ι) :
    (logPrimePeriod q i).im = Real.log (q i : ℕ) := by
  unfold logPrimePeriod
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [Fintype ι] in
/-- Prime logarithms are positive, so the periods lie in the upper half plane. -/
theorem logPrimePeriod_im_pos (q : ι → Nat.Primes) (i : ι) : 0 < (logPrimePeriod q i).im := by
  rw [logPrimePeriod_im]
  exact Real.log_pos (by exact_mod_cast (q i).2.one_lt)

/-- **No integral relation between `1` and imaginary prime-log periods.**  The real part of a
relation is its coefficient of `1`, and the imaginary part is an integral relation between
logarithms of distinct primes, which unique factorization forbids. -/
theorem periodsIntegrallyIndependent_logPrimePeriod {q : ι → Nat.Primes}
    (hq : Function.Injective q) : PeriodsIntegrallyIndependent (logPrimePeriod q) := by
  classical
  intro m n hrel
  have hre : (m : ℝ) = 0 := by
    have h := congrArg Complex.re hrel
    simpa only [Complex.add_re, Complex.re_sum, Complex.intCast_re, Complex.intCast_im,
      Complex.zero_re, Complex.mul_re, logPrimePeriod_re, logPrimePeriod_im, mul_zero, zero_mul,
      sub_zero, Finset.sum_const_zero, add_zero] using h
  have him : ∑ i, (n i : ℝ) * Real.log (q i : ℕ) = 0 := by
    have h := congrArg Complex.im hrel
    simpa only [Complex.add_im, Complex.im_sum, Complex.intCast_re, Complex.intCast_im,
      Complex.zero_im, Complex.mul_im, logPrimePeriod_re, logPrimePeriod_im, mul_zero, zero_mul,
      add_zero, zero_add] using h
  have hind : LinearIndependent ℤ fun i : ι => Real.log (q i : ℕ) :=
    logPrime_linearIndependent_int.comp q hq
  have hzero : ∀ i ∈ (univ : Finset ι), n i = 0 := by
    refine linearIndependent_iff'.mp hind univ n ?_
    simpa [zsmul_eq_mul] using him
  exact ⟨by exact_mod_cast hre, fun i => hzero i (mem_univ i)⟩

/-- **Realization.**  Over any finite index there are periods in the upper half plane admitting no
integral relation with `1`. -/
theorem exists_periods_im_pos_integrallyIndependent (ι : Type) [Fintype ι] :
    ∃ τ : ι → ℂ, (∀ i, 0 < (τ i).im) ∧ PeriodsIntegrallyIndependent τ := by
  classical
  set e : ι ↪ Nat.Primes :=
    ((Fintype.equivFin ι).toEmbedding.trans Fin.valEmbedding).trans
      (Infinite.natEmbedding Nat.Primes) with he
  exact ⟨logPrimePeriod e, logPrimePeriod_im_pos _, periodsIntegrallyIndependent_logPrimePeriod
    e.injective⟩

/-! ### The pair restriction -/

/-- **Connector.**  The rank-three source hypothesis of the elliptic gamma packet — rational
independence of `1` and two periods — is the two-parameter restriction of the lattice hypothesis.
Denominators are cleared by localizing the integral statement. -/
theorem linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ) {a b : ι} (hab : a ≠ b) :
    LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)) := by
  classical
  have hint : LinearIndependent ℤ (ellipticGammaSourcePeriods (τ a) (τ b)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set n : ι → ℤ := fun i => if i = a then g 1 else if i = b then g 2 else 0 with hn
    have hsum : (g 0 : ℂ) + ∑ i, (n i : ℂ) * τ i = 0 := by
      have hsub : ∑ i, (n i : ℂ) * τ i = ∑ i ∈ ({a, b} : Finset ι), (n i : ℂ) * τ i := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro i _ hi
        have hia : i ≠ a := fun h => hi (by simp [h])
        have hib : i ≠ b := fun h => hi (by simp [h])
        simp [hn, hia, hib]
      rw [hsub, Finset.sum_pair hab]
      have hna : n a = g 1 := by simp [hn]
      have hnb : n b = g 2 := by simp [hn, hab.symm]
      rw [hna, hnb]
      have := hg
      simp only [Fin.sum_univ_three, ellipticGammaSourcePeriods, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        zsmul_eq_mul, mul_one] at this
      linear_combination this
    obtain ⟨hg0, hgn⟩ := hQ (g 0) n hsum
    have h1 : g 1 = 0 := by simpa [hn] using hgn a
    have h2 : g 2 = 0 := by simpa [hn, hab.symm] using hgn b
    intro i
    fin_cases i
    · exact hg0
    · exact h1
    · exact h2
  exact hint.localization ℚ (nonZeroDivisors ℤ)

/-- The rank-three source hypothesis on explicit periods. -/
theorem linearIndependent_ellipticGammaSourcePeriods_logPrime {p r : Nat.Primes} (hpr : p ≠ r) :
    LinearIndependent ℚ (ellipticGammaSourcePeriods
      (Complex.I * (Real.log (p : ℕ) : ℂ)) (Complex.I * (Real.log (r : ℕ) : ℂ))) := by
  classical
  have hq : Function.Injective (fun x : Bool => if x then p else r) := by
    intro x y hxy
    cases x <;> cases y <;> simp_all
  have := linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
    (logPrimePeriod fun x : Bool => if x then p else r)
    (periodsIntegrallyIndependent_logPrimePeriod hq) (a := true) (b := false) (by simp)
  simpa [logPrimePeriod] using this

end GaloisForLFunctions.HTGeometry
