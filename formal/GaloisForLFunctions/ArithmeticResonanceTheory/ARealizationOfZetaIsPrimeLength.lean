import GaloisForLFunctions.ArithmeticResonanceTheory.GeneralizedDirichletSeriesAreDeterminedByTheirValues
import GaloisForLFunctions.ArithmeticResonanceTheory.TheHolderModulusOfAPrimeLengthSystem
import GaloisForLFunctions.ArithmeticResonanceTheory.AHolderRealizationIsAZeroFreeStrip

/-!
# A realization of `ζ` is a prime-length system

Let `φ ≥ r_min > 0` be a roof on a subshift of finite type whose dynamical zeta function equals
`ζ`: `ζ(s) = exp Σ_{n ≥ 1} Z_n(s)/n` on `Re s > 1`, with `Z_n(s) = Σ_{σⁿx = x} e^{−s φⁿ(x)}`.

On the real axis both sides of `log ζ(σ)` are generalized Dirichlet series with positive
coefficients: the dynamical side `Σ_{(n, x)} n⁻¹ e^{−σ φⁿ(x)}` over periodic points
(`hasSum_orbitSide`), the arithmetic side `Σ_{(p, k)} (k+1)⁻¹ e^{−σ (k+1) log p}` over prime powers
(`hasSum_primeSide`). Both have locally finite frequencies (`φⁿ ≥ n r_min`; `(k+1) log p ≥ (k+1) log 2`),
so by uniqueness (`massAt_eq_zero_of_tsum_eq_zero`) their masses agree at every length.

**Theorem** (`isPrimeLength_of_realization`). Every such realization is prime-length. A periodic
point `x` of least period `L` contributes its `L` shifts, each with weight `1/L`, at the length
`t = φ^L(x)`: mass at least `1`. On the arithmetic side the length `t` is carried by at most one
prime power `p^{k+1}` (unique factorization), with mass `1/(k+1)`. Equality forces `k = 0`:
`e^t = p`.

**Corollary** (`one_le_exp_mul_of_holderRealization`, *the price of the strip*). A realization of
`ζ` by a `θ`-Hölder roof on a mixing subshift gives a zero-free strip
(`riemannZeta_ne_zero_of_holderRealization`), and at every fixed point `a` that can be left and
re-entered it has `θ · e^{φ(a^∞)} ≥ 1`.
-/

open Filter Topology Finset
open GaloisForLFunctions.HTGeometry.Symbolic

namespace GaloisForLFunctions.ArithmeticResonanceTheory

variable {k : ℕ} {A : Fin k → Fin k → Prop} {φ : (ℕ → Fin k) → ℝ}

/-! ## The two sides as generalized Dirichlet series -/

/-- Periodic points of period `n + 1`, indexed together. -/
abbrev OrbitIndex (A : Fin k → Fin k → Prop) := Σ n : ℕ, ↥(periodicPoints A (n + 1))

/-- Weight `1/(n + 1)` of a periodic point of period `n + 1`. -/
noncomputable def orbitWeight (i : OrbitIndex A) : ℝ := 1 / ((i.1 : ℝ) + 1)

/-- Length `φ^{n+1}(x)` of a periodic point of period `n + 1`. -/
noncomputable def orbitLength (φ : (ℕ → Fin k) → ℝ) (i : OrbitIndex A) : ℝ :=
  birkhoff φ (i.1 + 1) i.2

/-- Weight `1/(k + 1)` of the prime power `p^{k+1}`. -/
noncomputable def primeWeight (q : Nat.Primes × ℕ) : ℝ := 1 / ((q.2 : ℝ) + 1)

/-- Length `(k + 1) log p` of the prime power `p^{k+1}`. -/
noncomputable def primeLength (q : Nat.Primes × ℕ) : ℝ := ((q.2 : ℝ) + 1) * Real.log (q.1 : ℕ)

theorem orbitWeight_pos (i : OrbitIndex A) : 0 < orbitWeight i := by
  unfold orbitWeight; positivity

theorem primeWeight_pos (q : Nat.Primes × ℕ) : 0 < primeWeight q := by
  unfold primeWeight; positivity

theorem log_prime_pos (p : Nat.Primes) : 0 < Real.log (p : ℕ) :=
  Real.log_pos (by exact_mod_cast p.prop.one_lt)

/-- The dynamical side: `Σ_{(n,x)} n⁻¹ e^{−σ φⁿ(x)} = Σ_n Z_n(σ)/n`. -/
theorem hasSum_orbitSide {σ : ℝ}
    (hsum : Summable fun n : ℕ => periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1)) :
    HasSum (fun i : OrbitIndex A => orbitWeight i * Real.exp (-(σ * orbitLength φ i)))
      (∑' n : ℕ, periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1)) := by
  have hnn : ∀ i : OrbitIndex A, 0 ≤ orbitWeight i * Real.exp (-(σ * orbitLength φ i)) :=
    fun i => mul_nonneg (orbitWeight_pos i).le (Real.exp_pos _).le
  have hfiber : ∀ n : ℕ, ∑' x : ↥(periodicPoints A (n + 1)),
      orbitWeight (⟨n, x⟩ : OrbitIndex A) * Real.exp (-(σ * orbitLength φ ⟨n, x⟩)) =
        periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1) := by
    intro n
    rw [tsum_fintype, periodicSumR, Finset.sum_div]
    rw [← Finset.sum_coe_sort (periodicPoints A (n + 1))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [orbitWeight, orbitLength]
    ring
  have hs : Summable fun i : OrbitIndex A => orbitWeight i * Real.exp (-(σ * orbitLength φ i)) :=
    (summable_sigma_of_nonneg hnn).mpr ⟨fun n => (Set.toFinite _).summable,
      by simpa only [hfiber] using hsum⟩
  rw [← (hs.tsum_sigma' fun n => (Set.toFinite _).summable).trans (tsum_congr hfiber)]
  exact hs.hasSum

/-- `e^{−σ(k+1) log p} = (p^{−σ})^{k+1}`. -/
theorem exp_neg_primeLength (σ : ℝ) (q : Nat.Primes × ℕ) :
    Real.exp (-(σ * primeLength q)) = (((q.1 : ℕ) : ℝ) ^ (-σ)) ^ (q.2 + 1) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast q.1.prop.pos), ← Real.exp_nat_mul, primeLength]
  congr 1
  push_cast
  ring

/-- The arithmetic side: `Σ_{(p,k)} (k+1)⁻¹ p^{−(k+1)σ} = Σ_p −log(1 − p^{−σ})`. -/
theorem hasSum_primeSide {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun q : Nat.Primes × ℕ => primeWeight q * Real.exp (-(σ * primeLength q)))
      (∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-σ))) := by
  set x : Nat.Primes → ℝ := fun p => ((p : ℕ) : ℝ) ^ (-σ) with hx
  have hx0 : ∀ p, 0 ≤ x p := fun p => Real.rpow_nonneg (by positivity) _
  have hxhalf : ∀ p, x p ≤ 1 / 2 := fun p => by
    calc x p ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos two_pos (by exact_mod_cast p.prop.two_le) (by linarith)
      _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one, one_div]
  have hxs : Summable x := Nat.Primes.summable_rpow.mpr (by linarith)
  have hterm : ∀ q : Nat.Primes × ℕ, primeWeight q * Real.exp (-(σ * primeLength q)) =
      x q.1 ^ (q.2 + 1) / ((q.2 : ℝ) + 1) := fun q => by
    rw [exp_neg_primeLength, primeWeight]; ring
  have hnn : ∀ q : Nat.Primes × ℕ, 0 ≤ x q.1 ^ (q.2 + 1) / ((q.2 : ℝ) + 1) :=
    fun q => div_nonneg (pow_nonneg (hx0 _) _) (by positivity)
  -- domination by `x_p (1/2)^k`
  have hs : Summable fun q : Nat.Primes × ℕ => x q.1 ^ (q.2 + 1) / ((q.2 : ℝ) + 1) := by
    refine Summable.of_nonneg_of_le hnn (fun q => ?_) (Summable.mul_of_nonneg hxs
      summable_geometric_two hx0 (fun _ => by positivity))
    have h1 : (1 : ℝ) ≤ (q.2 : ℝ) + 1 := by linarith [(Nat.cast_nonneg q.2 : (0 : ℝ) ≤ q.2)]
    calc x q.1 ^ (q.2 + 1) / ((q.2 : ℝ) + 1) ≤ x q.1 ^ (q.2 + 1) :=
          div_le_self (pow_nonneg (hx0 _) _) h1
      _ = x q.1 * x q.1 ^ q.2 := by ring
      _ ≤ x q.1 * (1 / 2) ^ q.2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hx0 _) (hxhalf _) _) (hx0 _)
  have hfiber : ∀ p : Nat.Primes, HasSum (fun j : ℕ => x p ^ (j + 1) / ((j : ℝ) + 1))
      (-Real.log (1 - x p)) := fun p => by
    have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := x p)
      (abs_lt.mpr ⟨by linarith [hx0 p], by linarith [hxhalf p]⟩)
    exact h
  simp_rw [hterm]
  have htot := hs.hasSum
  rw [hs.tsum_prod' (fun p => (hfiber p).summable), tsum_congr fun p => (hfiber p).tsum_eq] at htot
  exact htot

/-! ## Local finiteness -/

theorem birkhoff_ge_of_admissible {rmin : ℝ} (hmin : ∀ y, IsAdmissible A y → rmin ≤ φ y)
    {x : ℕ → Fin k} (hx : IsAdmissible A x) (n : ℕ) : n * rmin ≤ birkhoff φ n x := by
  rw [birkhoff]
  calc (n : ℝ) * rmin = ∑ _i ∈ Finset.range n, rmin := by simp
    _ ≤ ∑ i ∈ Finset.range n, φ (shiftBy i x) :=
        Finset.sum_le_sum fun i _ => hmin _ (hx.shiftBy i)

/-- The combined signed series: periodic points with weight `+1/n`, prime powers with `−1/(k+1)`. -/
noncomputable def signedWeight (A : Fin k → Fin k → Prop) :
    OrbitIndex A ⊕ (Nat.Primes × ℕ) → ℝ :=
  Sum.elim orbitWeight fun q => -primeWeight q

noncomputable def signedLength (φ : (ℕ → Fin k) → ℝ) :
    OrbitIndex A ⊕ (Nat.Primes × ℕ) → ℝ :=
  Sum.elim (orbitLength φ) primeLength

theorem signedLength_finite {rmin : ℝ} (hrmin : 0 < rmin)
    (hmin : ∀ y, IsAdmissible A y → rmin ≤ φ y) (T : ℝ) :
    {i | signedLength (A := A) φ i ≤ T}.Finite := by
  classical
  -- periods up to `T / r_min`, primes up to `e^T`, exponents up to `T / log 2`
  obtain ⟨N, hN⟩ := exists_nat_gt (T / rmin)
  obtain ⟨P, hP⟩ := exists_nat_gt (Real.exp T)
  obtain ⟨K, hK⟩ := exists_nat_gt (T / Real.log 2)
  set S₁ : Finset (OrbitIndex A) := (Finset.range N).sigma fun _ => Finset.univ with hS₁
  set S₂ : Finset (Nat.Primes × ℕ) :=
    ((Finset.range P).subtype Nat.Prime) ×ˢ Finset.range K with hS₂
  refine (S₁.disjSum S₂).finite_toSet.subset fun i hi => ?_
  simp only [Set.mem_setOf_eq] at hi
  rcases i with ⟨n, x⟩ | ⟨p, j⟩
  · simp only [signedLength, Sum.elim_inl, orbitLength] at hi
    have hx := (mem_periodicPoints.mp x.2).1
    have h1 := birkhoff_ge_of_admissible hmin hx (n + 1)
    have hn : (n : ℝ) < N := by
      have : ((n + 1 : ℕ) : ℝ) * rmin ≤ T := h1.trans hi
      rw [div_lt_iff₀ hrmin] at hN ⊢
      push_cast at this
      nlinarith
    simp only [Finset.coe_disjSum, Set.mem_union, Set.mem_image, Finset.mem_coe, hS₁,
      Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true]
    left; exact ⟨⟨n, x⟩, by exact_mod_cast hn, rfl⟩
  · simp only [signedLength, Sum.elim_inr, primeLength] at hi
    have hlog := log_prime_pos p
    have hlog2 : Real.log 2 ≤ Real.log (p : ℕ) :=
      Real.log_le_log two_pos (by exact_mod_cast p.prop.two_le)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hpT : Real.log (p : ℕ) ≤ T := by nlinarith
    have hp : ((p : ℕ) : ℝ) < P := by
      calc ((p : ℕ) : ℝ) = Real.exp (Real.log (p : ℕ)) :=
            (Real.exp_log (by exact_mod_cast p.prop.pos)).symm
        _ ≤ Real.exp T := Real.exp_le_exp.mpr hpT
        _ < P := hP
    have hj : (j : ℝ) < K := by
      have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      rw [div_lt_iff₀ hl2] at hK
      nlinarith
    simp only [Finset.coe_disjSum, Set.mem_union, Set.mem_image, Finset.mem_coe, hS₂,
      Finset.mem_product, Finset.mem_subtype, Finset.mem_range]
    right; exact ⟨⟨p, j⟩, ⟨by exact_mod_cast hp, by exact_mod_cast hj⟩, rfl⟩

/-! ## Realizations are prime-length -/

/-- The Birkhoff sum over a full period is shift invariant. -/
theorem birkhoff_shiftBy_of_period {L : ℕ} {y : ℕ → Fin k} (hy : shiftBy L y = y) (j : ℕ) :
    birkhoff φ L (shiftBy j y) = birkhoff φ L y := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hyj : shiftBy L (shiftBy j y) = shiftBy j y := by
      rw [shiftBy_shiftBy, Nat.add_comm, ← shiftBy_shiftBy, hy]
    have h1 := birkhoff_add φ 1 L (shiftBy j y)
    have h2 := birkhoff_add φ L 1 (shiftBy j y)
    rw [Nat.add_comm 1 L, hyj] at h1
    rw [shiftBy_shiftBy, Nat.add_comm] at h1
    rw [← ih]
    linarith

/-- **A realization of `ζ` is prime-length.** -/
theorem isPrimeLength_of_realization {rmin : ℝ} (hrmin : 0 < rmin)
    (hmin : ∀ y, IsAdmissible A y → rmin ≤ φ y)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1))
    (hreal : ∀ s : ℂ, 1 < s.re →
      riemannZeta s = Complex.exp (∑' n : ℕ, periodicZ A φ (n + 1) s / ((n : ℂ) + 1))) :
    IsPrimeLength A φ := by
  classical
  -- on the real axis the two logarithms of `ζ(σ)` agree
  have hlog : ∀ σ : ℝ, 1 < σ → ∑' n : ℕ, periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1) =
      ∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-σ)) := by
    intro σ hσ
    have hre : 1 < (σ : ℂ).re := by simpa using hσ
    have h1 := hreal σ hre
    have h2 := riemannZeta_eulerProduct_exp_log hre
    rw [h1] at h2
    have hL : ∑' n : ℕ, periodicZ A φ (n + 1) (σ : ℂ) / ((n : ℂ) + 1) =
        ((∑' n : ℕ, periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun n => by rw [periodicZ_ofReal]; push_cast; ring
    have hR : ∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(σ : ℂ))) =
        ((∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun p => ?_
      have hx : ((p : ℕ) : ℝ) ^ (-σ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
      rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_cpow (by positivity), Complex.ofReal_neg,
        Complex.ofReal_natCast]
    rw [hL, hR, ← Complex.ofReal_exp, ← Complex.ofReal_exp] at h2
    exact Real.exp_injective (Complex.ofReal_injective h2)
  -- the signed series vanishes, so its masses vanish
  have hfin := signedLength_finite (A := A) hrmin hmin
  have hzero : ∀ t, massAt (signedWeight A) (signedLength φ) hfin t = 0 := by
    refine massAt_eq_zero_of_tsum_eq_zero _ _ hfin (σ₀ := 1) (fun σ hσ => ?_) (fun σ hσ => ?_)
    · refine Summable.sum _ ?_ ?_
      · simpa [signedWeight, signedLength, Function.comp_def,
          abs_of_pos (orbitWeight_pos _)] using (hasSum_orbitSide (hsum σ hσ)).summable
      · simpa [signedWeight, signedLength, Function.comp_def,
          abs_of_pos (primeWeight_pos _)] using (hasSum_primeSide (A := A) hσ).summable
    · have h := HasSum.sum (f := fun i => signedWeight A i * Real.exp (-(σ * signedLength φ i)))
        (by simpa [signedWeight, signedLength, Function.comp_def] using
          hasSum_orbitSide (hsum σ hσ))
        (by simpa [signedWeight, signedLength, Function.comp_def, neg_mul] using
          (hasSum_primeSide (A := A) hσ).neg)
      rw [h.tsum_eq, hlog σ hσ, add_neg_cancel]
  -- the atom of a periodic point
  intro x hx L hL hmin'
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  set t := birkhoff φ (m + 1) x with ht
  have hper : shiftBy (m + 1) x = x := by
    have h := Function.isPeriodicPt_minimalPeriod (shiftBy 1) x
    rw [hmin', Function.IsPeriodicPt, Function.IsFixedPt, shiftBy_one_iterate] at h
    exact h
  have hmemj : ∀ j, shiftBy j x ∈ periodicPoints A (m + 1) := fun j =>
    mem_periodicPoints.mpr ⟨hx.shiftBy j, by rw [shiftBy_shiftBy, Nat.add_comm,
      ← shiftBy_shiftBy, hper]⟩
  set fib := (hfin t).toFinset.filter fun i => signedLength φ i = t with hfib
  have hsplit := hzero t
  rw [massAt, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight] at hsplit
  simp only [signedWeight, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib] at hsplit
  -- the orbit of `x` gives mass at least `1`
  set orb : ℕ → OrbitIndex A := fun j => ⟨m, ⟨shiftBy j x, hmemj j⟩⟩ with horb
  have horb_inj : Set.InjOn orb (Finset.range (m + 1)) := by
    intro i hi j hj hij
    have hij' : shiftBy i x = shiftBy j x := by
      have := congrArg (fun o : OrbitIndex A => (o.2 : ℕ → Fin k)) hij
      simpa [horb] using this
    by_contra hne
    wlog hlt : i < j generalizing i j
    · exact this hj hi hij'.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    -- `j − i` would be a period below the least period
    have hperiod : shiftBy (j - i) x = x := by
      have h1 := congrArg (shiftBy (m + 1 - i)) hij'
      rw [shiftBy_shiftBy, shiftBy_shiftBy, show m + 1 - i + i = m + 1 by omega,
        show m + 1 - i + j = (j - i) + (m + 1) by omega, ← shiftBy_shiftBy, hper] at h1
      exact h1.symm
    have hpt : Function.IsPeriodicPt (shiftBy 1) (j - i) x := by
      rw [Function.IsPeriodicPt, Function.IsFixedPt, shiftBy_one_iterate, hperiod]
    have := Nat.le_of_dvd (by omega) (hpt.minimalPeriod_dvd)
    rw [hmin'] at this
    omega
  have horb_mem : ∀ j ∈ Finset.range (m + 1), orb j ∈ fib.toLeft := by
    intro j _
    rw [Finset.mem_toLeft, hfib, mem_massAt_finset]
    simp only [signedLength, Sum.elim_inl, orbitLength, horb]
    exact birkhoff_shiftBy_of_period hper j
  have hleft : 1 ≤ ∑ a ∈ fib.toLeft, orbitWeight a := by
    calc (1 : ℝ) = ∑ j ∈ Finset.range (m + 1), orbitWeight (orb j) := by
          simp only [horb, orbitWeight, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; field_simp
      _ = ∑ a ∈ (Finset.range (m + 1)).image orb, orbitWeight a :=
          (Finset.sum_image horb_inj).symm
      _ ≤ ∑ a ∈ fib.toLeft, orbitWeight a :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun a ha => by obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha; exact horb_mem j hj)
            fun a _ _ => (orbitWeight_pos a).le
  -- the arithmetic side carries the length `t` at most once
  have hright_le : fib.toRight.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun q hq q' hq' => ?_
    rw [Finset.mem_toRight, hfib, mem_massAt_finset] at hq hq'
    simp only [signedLength, Sum.elim_inr, primeLength] at hq hq'
    have heq : ((q.2 : ℝ) + 1) * Real.log (q.1 : ℕ) = ((q'.2 : ℝ) + 1) * Real.log (q'.1 : ℕ) := by
      rw [hq, hq']
    have hpow : ((q.1 : ℕ) ^ (q.2 + 1) : ℕ) = ((q'.1 : ℕ) ^ (q'.2 + 1) : ℕ) := by
      have h1 : Real.log (((q.1 : ℕ) ^ (q.2 + 1) : ℕ) : ℝ) =
          Real.log (((q'.1 : ℕ) ^ (q'.2 + 1) : ℕ) : ℝ) := by
        push_cast; rw [Real.log_pow, Real.log_pow]; push_cast; linarith
      have h2 := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) h1
      exact_mod_cast h2
    obtain ⟨hp, hk⟩ := Nat.Prime.pow_inj q.1.prop q'.1.prop hpow
    exact Prod.ext (Subtype.ext hp) hk
  have hright_ge : 1 ≤ ∑ q ∈ fib.toRight, primeWeight q := by linarith
  -- so the length `t` is `log p` for a prime `p`, with exponent `1`
  obtain ⟨q, hq⟩ : fib.toRight.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hright_ge
    linarith
  have hsingle : fib.toRight = {q} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hq, fun q' hq' =>
      Finset.card_le_one.mp hright_le q' hq' q hq⟩
  rw [hsingle, Finset.sum_singleton, primeWeight] at hright_ge
  have hk : q.2 = 0 := by
    by_contra hk
    have : (1 : ℝ) < (q.2 : ℝ) + 1 := by
      have : (1 : ℝ) ≤ q.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      linarith
    rw [le_div_iff₀ (by positivity)] at hright_ge
    linarith
  have hlen : t = Real.log (q.1 : ℕ) := by
    have h := hq
    rw [Finset.mem_toRight, hfib, mem_massAt_finset] at h
    simp only [signedLength, Sum.elim_inr, primeLength, hk, Nat.cast_zero, zero_add,
      one_mul] at h
    exact h.symm
  refine ⟨q.1, q.1.prop, ?_⟩
  rw [← ht, hlen, Real.exp_log (by exact_mod_cast q.1.prop.pos)]

/-! ## The price of the strip -/

/-- **The price of the strip.** A realization of `ζ` by a `(C, θ)`-Hölder roof on a mixing
subshift of finite type gives `ζ ≠ 0` on a half-plane `Re s > 1 − ε`; and at every fixed point
`a` that can be left to a symbol `b ≠ a` and re-entered, its Hölder modulus satisfies
`θ · e^{φ(a^∞)} ≥ 1`. -/
theorem one_le_exp_mul_of_holderRealization {M : ℕ} (hmix : IsMixing A M) (hM : 1 ≤ M)
    {R₀ C θ : ℝ} (hφ : IsHolderPotential A φ R₀ C θ) (hR₀ : 0 ≤ R₀) (hC : 0 ≤ C) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {rmin : ℝ} (hrmin : 0 < rmin) (hmin : ∀ y, IsAdmissible A y → rmin ≤ φ y)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1))
    (hreal : ∀ s : ℂ, 1 < s.re →
      riemannZeta s = Complex.exp (∑' n : ℕ, periodicZ A φ (n + 1) s / ((n : ℂ) + 1)))
    {a b : Fin k} (hab : a ≠ b) (haa : A a a) (hab' : A a b) (hba : A b a) :
    (∃ ε > 0, ∀ s : ℂ, 1 - ε < s.re → s ≠ 1 → riemannZeta s ≠ 0) ∧
      1 ≤ Real.exp (φ (fun _ => a)) * θ :=
  ⟨riemannZeta_ne_zero_of_holderRealization hmix hM hφ hR₀ hC hθ0 hθ1 hrmin hmin hsum hreal,
    one_le_exp_mul_of_isPrimeLength hθ0.le hθ1 hφ.holder
      (isPrimeLength_of_realization hrmin hmin hsum hreal) hab haa hab' hba⟩

end GaloisForLFunctions.ArithmeticResonanceTheory
