import GaloisForLFunctions.HTGeometry.DirichletHypertranscendence
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.PrimeCounting

/-!
# Zeta has no differential relation with Gamma-field coefficients

On a vertical strip inside `Re s > 1` the Riemann zeta function is the uniform limit of the partial
sums of its Dirichlet series, so it is almost periodic there, and its Bohr spectrum on a line
contains `-log p` for every prime `p`.  Unique factorization makes any finite set of those
frequencies `ℤ`-independent, so the rational frequency rank of the line restriction exceeds every
natural number.  The finite phase law then forbids every nontrivial differential relation whose
coefficients lie in the Gamma field: zeta is hypertranscendental over `ℂ(s)⟨Γ⟩`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

open _root_.HTGeometry

open scoped BoundedContinuousFunction

/-! ### The Dirichlet series of zeta -/

/-- The Dirichlet exponential of frequency `log (i + 1)` is the `(i+1)`-st term of the zeta
series. -/
theorem exp_neg_log_succ_mul (i : ℕ) (z : ℂ) :
    Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z) = 1 / ((i : ℂ) + 1) ^ z := by
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hb : ((i : ℂ) + 1) ≠ 0 := by
    have h : ((i : ℝ) + 1 : ℂ) = (i : ℂ) + 1 := by push_cast; ring
    rw [← h]
    exact_mod_cast (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
  rw [Complex.cpow_def_of_ne_zero hb]
  rw [one_div, ← Complex.exp_neg]
  congr 1
  have hlog : Complex.log ((i : ℂ) + 1) = ((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) := by
    have hcast : ((i : ℂ) + 1) = (((i : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_log hpos.le]
  rw [hlog]
  ring

/-- The norm of a zeta term is a real power of its index. -/
theorem norm_zeta_term (i : ℕ) (z : ℂ) :
    ‖(1 : ℂ) / ((i : ℂ) + 1) ^ z‖ = 1 / ((i : ℝ) + 1) ^ z.re := by
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hcast : ((i : ℂ) + 1) = (((i : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  simp

/-- The comparison series governing the zeta terms on the half-plane `Re z ≥ c`. -/
theorem summable_zeta_compare {c : ℝ} (hc : 1 < c) :
    Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ c) := by
  have h := (Real.summable_one_div_nat_rpow (p := c)).mpr hc
  have h1 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ c) 1).mpr h
  refine h1.congr (fun i => ?_)
  push_cast
  ring_nf

/-- On the half-plane `Re z ≥ c` the zeta terms are dominated by the comparison series. -/
theorem norm_zeta_term_le {c : ℝ} (i : ℕ) {z : ℂ} (hz : c ≤ z.re) :
    ‖(1 : ℂ) / ((i : ℂ) + 1) ^ z‖ ≤ 1 / ((i : ℝ) + 1) ^ c := by
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have h1 : (1 : ℝ) ≤ (i : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  rw [norm_zeta_term i z]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hpos c)
    (Real.rpow_le_rpow_of_exponent_le h1 hz)

/-- The zeta series converges absolutely on `Re z ≥ c` for `c > 1`. -/
theorem summable_zeta_terms {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : c ≤ z.re) :
    Summable (fun i : ℕ => (1 : ℂ) / ((i : ℂ) + 1) ^ z) :=
  Summable.of_norm_bounded (summable_zeta_compare hc) (fun i => norm_zeta_term_le i hz)

/-- The absolute bound for zeta on the closed half-plane `Re z ≥ c`. -/
noncomputable def zetaHalfPlaneBound (c : ℝ) : ℝ := ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ c

/-- Zeta is bounded on every closed half-plane to the right of `1`. -/
theorem norm_riemannZeta_le_halfPlane {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : c ≤ z.re) :
    ‖riemannZeta z‖ ≤ zetaHalfPlaneBound c := by
  have hz1 : 1 < z.re := lt_of_lt_of_le hc hz
  have hs : Summable (fun i : ℕ => (1 : ℂ) / ((i : ℂ) + 1) ^ z) := summable_zeta_terms hc hz
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz1, zetaHalfPlaneBound]
  calc ‖∑' i : ℕ, (1 : ℂ) / ((i : ℂ) + 1) ^ z‖
      ≤ ∑' i : ℕ, ‖(1 : ℂ) / ((i : ℂ) + 1) ^ z‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ c :=
        Summable.tsum_le_tsum (fun i => norm_zeta_term_le i hz) hs.norm (summable_zeta_compare hc)

/-- **Uniform approximation of zeta by its Dirichlet partial sums.**  On a closed half-plane to the
right of `1`, every partial sum beyond a threshold approximates zeta to within `ε`. -/
theorem zeta_uniform_approx {c : ℝ} (hc : 1 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n₀ : ℕ, N ≤ n₀ → ∀ z : ℂ, c ≤ z.re →
      ‖riemannZeta z - ∑ i ∈ Finset.range n₀,
        (1 : ℂ) * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z)‖ ≤ ε := by
  classical
  set g : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1) ^ c with hgdef
  have hg : Summable g := summable_zeta_compare hc
  have htail : Filter.Tendsto (fun n => ∑' i, g (i + n)) Filter.atTop (nhds 0) :=
    tendsto_sum_nat_add g
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (htail.eventually (ge_mem_nhds (by simpa using hε)))
  refine ⟨N, fun n₀ hn₀ z hz => ?_⟩
  have hz1 : 1 < z.re := lt_of_lt_of_le hc hz
  set f : ℕ → ℂ := fun i => 1 / ((i : ℂ) + 1) ^ z with hfdef
  have hbound : ∀ i : ℕ, ‖f i‖ ≤ g i := fun i => norm_zeta_term_le i hz
  have hfs : Summable f := summable_zeta_terms hc hz
  have hzeta : riemannZeta z = ∑' i : ℕ, f i := zeta_eq_tsum_one_div_nat_add_one_cpow hz1
  have hsum : ∑ i ∈ Finset.range n₀, f i + ∑' i, f (i + n₀) = ∑' i, f i :=
    hfs.sum_add_tsum_nat_add n₀
  have hrw : ∑ i ∈ Finset.range n₀,
      (1 : ℂ) * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z)
      = ∑ i ∈ Finset.range n₀, f i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_mul, exp_neg_log_succ_mul i z]
  rw [hzeta, hrw, ← hsum]
  have hcancel : ∑ i ∈ Finset.range n₀, f i + ∑' i, f (i + n₀) - ∑ i ∈ Finset.range n₀, f i
      = ∑' i, f (i + n₀) := by ring
  rw [hcancel]
  have hshift : Summable (fun i => f (i + n₀)) := (summable_nat_add_iff n₀).mpr hfs
  have hgshift : Summable (fun i => g (i + n₀)) := (summable_nat_add_iff n₀).mpr hg
  calc ‖∑' i, f (i + n₀)‖ ≤ ∑' i, ‖f (i + n₀)‖ := norm_tsum_le_tsum_norm (by simpa using hshift.norm)
    _ ≤ ∑' i, g (i + n₀) := Summable.tsum_le_tsum (fun i => hbound _) hshift.norm hgshift
    _ ≤ ε := hN n₀ hn₀

/-- The Dirichlet approximation of zeta in the form required on a vertical strip inside
`Re z > 1`. -/
theorem zeta_dirichlet_conv {σ R : ℝ} (hRσ : R ≤ σ - 1) :
    ∀ r' : ℝ, r' < R → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ z ∈ closedStrip σ r',
      ‖riemannZeta z - ∑ i ∈ Finset.range n₀,
        (1 : ℂ) * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z)‖ ≤ ε := by
  intro r' hr' ε hε
  have hc : 1 < σ - r' := by linarith
  obtain ⟨N, hN⟩ := zeta_uniform_approx hc hε
  refine ⟨N, fun z hz => hN N le_rfl z ?_⟩
  have habs : |z.re - σ| ≤ r' := hz
  have := (abs_le.mp habs).1
  linarith

/-! ### Zeta on a vertical line -/

/-- Zeta is continuous on every vertical line to the right of `1`. -/
theorem continuous_zeta_line {σ : ℝ} (hσ : 1 < σ) :
    Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hin : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) t := by fun_prop
  exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
    (differentiableAt_riemannZeta hne).continuousAt hin

/-- Zeta restricted to a vertical line to the right of `1`, as a bounded continuous function. -/
noncomputable def zetaLine {σ : ℝ} (hσ : 1 < σ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) (continuous_zeta_line hσ)
    (zetaHalfPlaneBound σ) (fun _ => norm_riemannZeta_le_halfPlane hσ (by simp))

@[simp] theorem zetaLine_apply {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    zetaLine hσ t = riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := rfl

/-! ### Independence of the prime frequencies -/

/-- The `i`-th prime, as an index of the zeta series. -/
noncomputable def nthPrimeIndex (i : ℕ) : ℕ := Nat.nth Nat.Prime i - 1

/-- The frequency attached to the `i`-th prime index of the zeta series is the logarithm of the
`i`-th prime. -/
theorem nthPrimeIndex_cast (i : ℕ) :
    ((nthPrimeIndex i : ℕ) : ℝ) + 1 = ((Nat.nth Nat.Prime i : ℕ) : ℝ) := by
  have hp : 1 ≤ Nat.nth Nat.Prime i := (Nat.prime_nth_prime i).one_lt.le
  rw [nthPrimeIndex, Nat.cast_sub hp]
  push_cast
  ring

/-- Distinct indices give distinct primes. -/
theorem nthPrime_injective : Function.Injective (fun i : ℕ => Nat.nth Nat.Prime i) :=
  Nat.nth_injective Nat.infinite_setOf_prime

/-- The first `K + 1` primes, as an injective family. -/
noncomputable def firstPrimes (K : ℕ) : Fin (K + 1) → Nat.Primes :=
  fun i => ⟨Nat.nth Nat.Prime (i : ℕ), Nat.prime_nth_prime (i : ℕ)⟩

theorem firstPrimes_injective (K : ℕ) : Function.Injective (firstPrimes K) := by
  intro i j hij
  have h : Nat.nth Nat.Prime (i : ℕ) = Nat.nth Nat.Prime (j : ℕ) := congrArg Subtype.val hij
  exact Fin.ext (nthPrime_injective h)

/-- Unique factorization makes the first `K + 1` prime logarithms `ℚ`-independent. -/
theorem linearIndependent_log_firstPrimes (K : ℕ) : LinearIndependent ℚ
    (fun i : Fin (K + 1) => Real.log ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℝ)) := by
  have h : LinearIndependent ℚ ((fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ)) ∘ firstPrimes K) :=
    linearIndependent_log_primes.comp _ (firstPrimes_injective K)
  have heq : ((fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ)) ∘ firstPrimes K)
      = fun i : Fin (K + 1) => Real.log ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℝ) := rfl
  rw [heq] at h
  exact h

/-- The prime logarithms are independent over `ℤ` as well. -/
theorem linearIndependent_int_log_firstPrimes (K : ℕ) : LinearIndependent ℤ
    (fun i : Fin (K + 1) => Real.log ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℝ)) := by
  refine (linearIndependent_log_firstPrimes K).restrict_scalars ?_
  intro a b hab
  have h : ((a : ℚ)) = ((b : ℚ)) := by simpa [zsmul_eq_mul] using hab
  exact_mod_cast h

/-- The Dirichlet frequencies of zeta at the first `K + 1` primes are `ℤ`-independent. -/
theorem linearIndependent_neg_log_firstPrimes (K : ℕ) : LinearIndependent ℤ
    (fun i : Fin (K + 1) => -(Real.log ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℝ))) := by
  have hfun : ((fun _ : Fin (K + 1) => (-1 : ℤˣ)) •
        (fun i : Fin (K + 1) => Real.log ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℝ)))
      = (fun i : Fin (K + 1) => -(Real.log ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℝ))) := by
    funext i
    simp [Units.smul_def]
  have h := (linearIndependent_int_log_firstPrimes K).units_smul (fun _ : Fin (K + 1) => (-1 : ℤˣ))
  rw [hfun] at h
  exact h

/-- The zeta frequencies are pairwise distinct. -/
theorem zetaFrequency_injective : Function.Injective (fun i : ℕ => Real.log ((i : ℝ) + 1)) := by
  intro i j hij
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h : (i : ℝ) + 1 = (j : ℝ) + 1 :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hi) (Set.mem_Ioi.mpr hj) hij
  have hij' : (i : ℝ) = (j : ℝ) := by linarith
  exact_mod_cast hij'

/-! ### The hypertranscendence of zeta over the Gamma field -/

/-- **Zeta satisfies no differential relation with Gamma-field coefficients.**  On a vertical strip
inside `Re s > 1`, zeta is the uniform limit of its Dirichlet partial sums, hence almost periodic;
the logarithms of the primes are `ℤ`-independent members of its Bohr spectrum, so the frequency rank
of the line restriction exceeds every natural number; and the finite phase law then rules out every
nontrivial relation whose coefficients are Gamma-field elements. -/
theorem zeta_no_gammaField_relation {n N k r : ℕ} {σ R rr ρ : ℝ} (hσ : 1 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) (hRσ : R ≤ σ - 1)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → Fin k → ℕ) (p q : Fin N → Fin k → Polynomial ℂ)
    (E : Fin N → Fin k → Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ α i, q α i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ α i, GammaMonomialDominates (j α i) (p α i) (q α i) (E α i 0) jb pb qb Db)
    (β : Fin N)
    (hc : (∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db) ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ∑ i, gammaJetEltG σ (j α i) (p α i) (q α i) (E α i) t)
    (hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) riemannZeta s) ^ (e α i) = 0)
    (he : Function.Injective e) : False := by
  classical
  set a : ℕ → ℂ := fun _ => 1 with hadef
  set lam : ℕ → ℝ := fun i => Real.log ((i : ℝ) + 1) with hlamdef
  set f : ℝ →ᵇ ℂ := zetaLine hσ with hfdef
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  have hconv : ∀ r' : ℝ, r' < R → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ z ∈ closedStrip σ r',
      ‖riemannZeta z - ∑ i ∈ Finset.range n₀,
        a i * Complex.exp (-(lam i : ℂ) * z)‖ ≤ ε := zeta_dirichlet_conv hRσ
  have hD : DifferentiableOn ℂ riemannZeta (verticalStrip σ R) := by
    intro z hz
    have habs : |z.re - σ| < R := hz
    have h1 : σ - R < z.re := by
      have := (abs_lt.mp habs).1
      linarith
    have hne : z ≠ 1 := by
      intro h
      rw [h] at h1
      simp at h1
      linarith
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  have hfval : ∀ x : ℝ, f x = riemannZeta ((σ : ℂ) + (x : ℂ) * Complex.I) := fun _ => rfl
  have hfcont : Continuous fun x : ℝ => f x := continuous_zeta_line hσ
  have hap : IsStripAlmostPeriodic riemannZeta σ R :=
    isStripAlmostPeriodic_dirichlet a lam riemannZeta hconv
  have hline : IsBohrAlmostPeriodic
      fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := isBohrAlmostPeriodic_line hR hap
  have hfap : IsBohrAlmostPeriodic fun x : ℝ => f x := hline
  have hfu : UniformContinuous fun x : ℝ => f x :=
    uniformContinuous_of_isBohrAlmostPeriodic hfcont hfap
  have hftb : HasTotallyBoundedOrbit fun x : ℝ => f x :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hfcont hfap
  have hrank : ∀ K : ℕ, ∃ idx : Fin (K + 1) → ℕ, (∀ i, a (idx i) ≠ 0) ∧
      (∀ i : Fin (K + 1), ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, idx i < n₀ ∧ ∀ t : ℝ,
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ i' ∈ Finset.range n₀,
            a i' * Complex.exp (-(lam i' : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε) ∧
      LinearIndependent ℤ (fun i : Fin (K + 1) => -(lam (idx i))) := by
    intro K
    refine ⟨fun i => nthPrimeIndex (i : ℕ), fun _ => one_ne_zero, ?_, ?_⟩
    · intro i ε hε
      obtain ⟨M, hM⟩ := zeta_uniform_approx (c := σ) hσ hε
      refine ⟨max M (nthPrimeIndex (i : ℕ) + 1), lt_of_lt_of_le (Nat.lt_succ_self _)
        (le_max_right _ _), fun t => ?_⟩
      exact hM _ (le_max_left _ _) _ (by simp)
    · have hfun : (fun i : Fin (K + 1) => -(lam (nthPrimeIndex (i : ℕ))))
          = fun i : Fin (K + 1) => -(Real.log ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℝ)) := by
        funext i
        rw [hlamdef]
        simp only
        rw [nthPrimeIndex_cast]
      rw [hfun]
      exact linearIndependent_neg_log_firstPrimes K
  exact dirichlet_no_gammaField_relation (by linarith) hr hρ hrρ hR a lam riemannZeta
    zetaFrequency_injective hD hconv hfval hfu hftb hrank e F j p q E jb pb qb Db
    hq hqb hpb hdom β hc hF hrel he

end GaloisForLFunctions
