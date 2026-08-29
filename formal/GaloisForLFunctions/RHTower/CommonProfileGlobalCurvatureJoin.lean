import GaloisForLFunctions.RHTower.CommonProfileVacuumJoin
import GaloisForLFunctions.RHTower.CommonProfileBooleanAnchorCurvature
import GaloisForLFunctions.HTGeometry.SchwartzTranslation
import GaloisForLFunctions.HTGeometry.SchwartzCompactSupport
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The global join of the future response with the Boolean anchor curvature

Summing the density-weighted future response over all gaps turns the sieved physical occupancy
into the double Gram sum of a common packet.  The squarefree anchor factor is the divisibility
indicator, so the Boolean anchor-curvature law converts that double sum into the alternating
finite difference of the sifted energies.
-/

open scoped BigOperators FourierTransform SchwartzMap
open ArithmeticFunction

noncomputable section

namespace RHTower

/-! ## Boolean avoidance coordinates -/

/-- The Boolean avoidance coordinate of a prime. -/
def avoidanceCoordinate (p : ℕ) (x : ℤ) : ℝ := if (p : ℤ) ∣ x then 0 else 1

theorem coordinatePacketWeight_avoidance (N : ℕ) (x : ℤ) :
    ((coordinatePacketWeight N.primeFactors avoidanceCoordinate x : ℝ) : ℂ) =
      sieveIndicator N x := by
  rw [coordinatePacketWeight, sieveIndicator, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [avoidanceCoordinate]
  by_cases hp : (p : ℤ) ∣ x
  · rw [if_pos hp, if_pos hp, Complex.ofReal_zero]
  · rw [if_neg hp, if_neg hp, Complex.ofReal_one]

/-- Every prime of a squarefree modulus divides a product exactly when the modulus does. -/
theorem forall_primeFactors_dvd_iff {c : ℕ} (hc : Squarefree c) (x : ℤ) :
    (∀ p ∈ c.primeFactors, (p : ℤ) ∣ x) ↔ (c : ℤ) ∣ x := by
  constructor
  · intro hall
    have hnat : ∀ p ∈ c.primeFactors, p ∣ x.natAbs := fun p hp =>
      Int.natCast_dvd.1 (hall p hp)
    have hprod : (∏ p ∈ c.primeFactors, p) ∣ x.natAbs :=
      Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hnat
    rw [Nat.prod_primeFactors_of_squarefree hc] at hprod
    exact Int.natCast_dvd.2 hprod
  · intro hdvd p hp
    exact dvd_trans (Int.natCast_dvd_natCast.2 (Nat.dvd_of_mem_primeFactors hp)) hdvd

/-- **`(CG8)`.**  The common anchor weight of a squarefree anchor is the divisibility indicator of
the product of the two source indices. -/
theorem commonAnchorWeight_avoidance {c : ℕ} (hc : Squarefree c) (x y : ℤ) :
    commonAnchorWeight c.primeFactors avoidanceCoordinate x y =
      if (c : ℤ) ∣ x * y then 1 else 0 := by
  classical
  have hfactor : ∀ p ∈ c.primeFactors,
      (1 - avoidanceCoordinate p x * avoidanceCoordinate p y) =
        if (p : ℤ) ∣ x * y then 1 else 0 := by
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hdvdmul : ((p : ℤ) ∣ x * y) ↔ ((p : ℤ) ∣ x ∨ (p : ℤ) ∣ y) :=
      (Nat.prime_iff_prime_int.mp hpp).dvd_mul
    rw [avoidanceCoordinate, avoidanceCoordinate]
    by_cases hx : (p : ℤ) ∣ x
    · rw [if_pos hx, zero_mul, sub_zero, if_pos (hdvdmul.2 (Or.inl hx))]
    · by_cases hy : (p : ℤ) ∣ y
      · rw [if_neg hx, if_pos hy, mul_zero, sub_zero, if_pos (hdvdmul.2 (Or.inr hy))]
      · rw [if_neg hx, if_neg hy, mul_one, sub_self,
          if_neg (fun hcon => (hdvdmul.1 hcon).elim hx hy)]
  rw [commonAnchorWeight, Finset.prod_congr rfl hfactor, Finset.prod_boole]
  exact if_congr (forall_primeFactors_dvd_iff hc (x * y)) rfl rfl

/-! ## The global gap sum of the sieved occupancy -/

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One sifted Gram term of the common packet. -/
def gramTerm (g : ℤ → E) (c N : ℕ) (m n : ℤ) : ℂ :=
  if (c : ℤ) ∣ m * n then ((inner ℝ (g m) (g n) : ℝ) : ℂ) *
    (sieveIndicator N m * sieveIndicator N n) else 0

/-- With a finitely supported Gram realization the sieved occupancy is a finite sum. -/
theorem siftedOccupancy_eq_finset_sum (W : 𝓢(ℝ, ℂ)) (g : ℤ → E) (indices : Finset ℤ)
    (h : ℤ) (hg : ∀ m, m ∉ indices → g m = 0)
    (hW : ∀ m : ℤ, W (m : ℝ) = ((inner ℝ (g m) (g (m + h)) : ℝ) : ℂ)) (c N : ℕ) :
    siftedOccupancy W c N h = ∑ m ∈ indices, gramTerm g c N m (m + h) := by
  classical
  rw [siftedOccupancy]
  have hcongr : ∀ m : ℤ, (if (c : ℤ) ∣ m * (m + h) then
      W (m : ℝ) * (sieveIndicator N m * sieveIndicator N (m + h)) else 0) =
      gramTerm g c N m (m + h) := by
    intro m
    rw [gramTerm, hW m]
  rw [tsum_congr hcongr]
  refine tsum_eq_sum fun m hm => ?_
  rw [gramTerm, hg m hm]
  simp

/-- **The global gap sum is the double Gram sum.** -/
theorem sum_gaps_gramTerm (g : ℤ → E) (indices gaps : Finset ℤ)
    (hg : ∀ m, m ∉ indices → g m = 0)
    (hgaps : ∀ m ∈ indices, ∀ n ∈ indices, n - m ∈ gaps) (c N : ℕ) :
    ∑ h ∈ gaps, ∑ m ∈ indices, gramTerm g c N m (m + h) =
      ∑ m ∈ indices, ∑ n ∈ indices, gramTerm g c N m n := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hinj : Set.InjOn (fun h : ℤ => m + h) (gaps : Set ℤ) := fun a _ b _ hab => by
    simpa using hab
  have hsub : indices ⊆ gaps.image (fun h : ℤ => m + h) := by
    intro n hn
    refine Finset.mem_image.2 ⟨n - m, hgaps m hm n hn, by ring⟩
  have hzero : ∀ n ∈ gaps.image (fun h : ℤ => m + h), n ∉ indices →
      gramTerm g c N m n = 0 := by
    intro n _ hn
    rw [gramTerm, hg n hn]
    simp
  rw [← Finset.sum_image hinj, ← Finset.sum_subset hsub hzero]

/-! ## `(CG6)` -/

/-- **`(CG6)`.**  Summing the density-weighted future response over all gaps of a finitely
supported common Gram packet gives the Boolean anchor curvature of the sifted energies minus the
summed Euler vacuum. -/
theorem sum_gaps_rootDensity_mul_futureResponse (W : ℤ → 𝓢(ℝ, ℂ)) (g : ℤ → E)
    (indices gaps : Finset ℤ) (hg : ∀ m, m ∉ indices → g m = 0)
    (hgaps : ∀ m ∈ indices, ∀ n ∈ indices, n - m ∈ gaps)
    (hW : ∀ (h m : ℤ), (W h) (m : ℝ) = ((inner ℝ (g m) (g (m + h)) : ℝ) : ℂ))
    {c N : ℕ} (hc : Squarefree c) (hN : Squarefree N) (hcN : c.Coprime N) :
    (∑ h ∈ gaps, rootDensity c h * futureResponse (schwartzFrequencyWeight (W h)) c N h) =
      ((∑ D ∈ c.primeFactors.powerset, (-1 : ℝ) ^ D.card *
          commonProfileSiftedEnergy indices (N.primeFactors ∪ D) avoidanceCoordinate g : ℝ) : ℂ) -
        ∑ h ∈ gaps, rootDensity c h *
          (𝓕 ((W h) : ℝ → ℂ) 0 * survivalProduct N h) := by
  classical
  have hc0 : c ≠ 0 := hc.ne_zero
  have hstep : ∀ h ∈ gaps,
      rootDensity c h * futureResponse (schwartzFrequencyWeight (W h)) c N h =
        (∑ m ∈ indices, gramTerm g c N m (m + h)) -
          rootDensity c h * (𝓕 ((W h) : ℝ → ℂ) 0 * survivalProduct N h) := by
    intro h _
    rw [rootDensity_mul_futureResponse_schwartz (W h) hc0 hN hcN h,
      siftedOccupancy_eq_finset_sum (W h) g indices h hg (fun m => hW h m) c N]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib,
    sum_gaps_gramTerm g indices gaps hg hgaps c N]
  congr 1
  have hdisj : Disjoint N.primeFactors c.primeFactors :=
    (hcN.disjoint_primeFactors).symm
  have hcurv := commonGramBooleanAnchorCurvature indices N.primeFactors c.primeFactors hdisj
    avoidanceCoordinate g
  rw [← hcurv, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [gramTerm, commonAnchorWeight_avoidance hc m n]
  push_cast
  rw [← coordinatePacketWeight_avoidance N m, ← coordinatePacketWeight_avoidance N n]
  by_cases hcd : (c : ℤ) ∣ m * n
  · rw [if_pos hcd, if_pos hcd]
    push_cast
    ring
  · rw [if_neg hcd, if_neg hcd]
    push_cast
    ring

/-! ## Realizability of the common physical profile -/

/-- A smooth unit bump, one at the origin and vanishing at every nonzero integer. -/
def integerBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem integerBump_zero : integerBump 0 = 1 :=
  integerBump.one_of_mem_closedBall (by simp [integerBump])

theorem integerBump_eq_zero_of_one_le {x : ℝ} (hx : (1 : ℝ) ≤ |x|) : integerBump x = 0 := by
  refine integerBump.zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero]
  show (integerBump.rOut : ℝ) ≤ |x|
  have hr : integerBump.rOut = 1 / 2 := rfl
  rw [hr]
  linarith

/-- The unit bump as a Schwartz function. -/
def bumpSchwartz : 𝓢(ℝ, ℂ) :=
  GaloisForLFunctions.HTGeometry.schwartzOfCompactSupport
    (f := fun x : ℝ => ((integerBump x : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp integerBump.contDiff)
    (integerBump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))

@[simp] theorem bumpSchwartz_apply (x : ℝ) :
    bumpSchwartz x = ((integerBump x : ℝ) : ℂ) := rfl

/-- **Every finitely supported datum on the integers is the integer sampling of a Schwartz
profile.**  So the common-profile hypotheses of the physical layer are not vacuous. -/
theorem exists_schwartz_interpolating (v : ℤ → ℂ) (S : Finset ℤ) (hv : ∀ m, m ∉ S → v m = 0) :
    ∃ W : 𝓢(ℝ, ℂ), ∀ m : ℤ, W (m : ℝ) = v m := by
  classical
  refine ⟨∑ m ∈ S, v m • (SchwartzMap.translateCLM ℂ (-(m : ℝ)) bumpSchwartz), fun k => ?_⟩
  rw [sum_apply]
  have hterm : ∀ m ∈ S, (v m • (SchwartzMap.translateCLM ℂ (-(m : ℝ)) bumpSchwartz)) (k : ℝ) =
      if m = k then v k else 0 := by
    intro m _
    rw [_root_.smul_apply, SchwartzMap.translateCLM_apply, bumpSchwartz_apply]
    by_cases hmk : m = k
    · subst hmk
      rw [if_pos rfl, show ((m : ℝ) + -(m : ℝ)) = 0 from by ring, integerBump_zero]
      simp
    · rw [if_neg hmk, integerBump_eq_zero_of_one_le ?_, Complex.ofReal_zero, smul_zero]
      have hne : (k : ℤ) - m ≠ 0 := sub_ne_zero.2 fun hcon => hmk hcon.symm
      have h1 : (1 : ℤ) ≤ |(k : ℤ) - m| := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · rw [abs_of_neg hlt]; omega
        · rw [abs_of_pos hgt]; omega
      have hsub : ((k : ℝ) + -(m : ℝ)) = (((k : ℤ) - m : ℤ) : ℝ) := by push_cast; ring
      rw [hsub, ← Int.cast_abs]
      exact_mod_cast h1
  rw [Finset.sum_congr rfl hterm]
  by_cases hk : k ∈ S
  · rw [Finset.sum_ite_eq' S k (fun _ => v k), if_pos hk]
  · rw [hv k hk]
    exact Finset.sum_eq_zero fun m _ => by simp

/-- The common Gram profile of a finitely supported packet is realized by Schwartz profiles. -/
theorem exists_schwartz_gramProfile (g : ℤ → E) (indices : Finset ℤ)
    (hg : ∀ m, m ∉ indices → g m = 0) :
    ∃ W : ℤ → 𝓢(ℝ, ℂ),
      ∀ (h m : ℤ), (W h) (m : ℝ) = ((inner ℝ (g m) (g (m + h)) : ℝ) : ℂ) := by
  classical
  choose W hW using fun h : ℤ =>
    exists_schwartz_interpolating (fun m : ℤ => ((inner ℝ (g m) (g (m + h)) : ℝ) : ℂ)) indices
      (fun m hm => by rw [hg m hm]; simp)
  exact ⟨W, hW⟩

end RHTower
