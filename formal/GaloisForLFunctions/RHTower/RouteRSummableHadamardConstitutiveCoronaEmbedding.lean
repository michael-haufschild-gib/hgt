import GaloisForLFunctions.RHTower.RouteRPrimeHarmonicShiftInvariantNilradical
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryCoronaLandingNoGo

/-!
# Multiplicative Route-R defect inside the constitutive Gamma corona

The constitutive Gamma corona was built additively from all prime-indexed sequences modulo
summable sequences.  The summable Hadamard corona retains less: only bounded enumerated tails,
but with pointwise multiplication.  Reindexing by the prime enumeration gives an injective linear
map from the multiplicative corona into the established constitutive receiver.

Under this map, the nonzero square-zero prime-harmonic element is exactly the physical
constitutive Gamma harmonic class.  Every critical-wall class therefore has a unique oriented
lift to a stationary square-zero element of the Hadamard corona.  This is a coefficient-level
comparison, not merely an agreement of vanishing loci.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Reindex an enumerated bounded tail by the corresponding prime. -/
def routeRBoundedTraceToPrimeTrace :
    RouteRBoundedTraceSequence →ₗ[ℂ] PrimeTraceSequence where
  toFun a p := a (nthPrimeEquiv.symm p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reindexing carries absolutely summable bounded tails to the physical prime summable ideal. -/
theorem routeRBoundedTraceToPrimeTrace_mem_summableIdeal
    {a : RouteRBoundedTraceSequence}
    (ha : a ∈ routeRSummableBoundedTailIdeal) :
    routeRBoundedTraceToPrimeTrace a ∈ primeFirstTraceSummableIdeal := by
  change Summable (fun p : Nat.Primes => a (nthPrimeEquiv.symm p))
  change Summable (fun n : ℕ => ‖a n‖) at ha
  have ha' : Summable (fun n : ℕ => a n) := summable_norm_iff.mp ha
  exact nthPrimeEquiv.summable_iff.mp (by
    simpa [Function.comp_def] using ha')

/-- Raw quotient map from the bounded-tail Hadamard corona to the constitutive Gamma corona. -/
private def routeRSummableHadamardToConstitutiveCoronaFun
    (x : RouteRSummableHadamardCorona) : ConstitutiveGammaCorona :=
  Quotient.map (fun a => routeRBoundedTraceToPrimeTrace a) (by
    intro a b hab
    apply Quotient.exact
    apply (Submodule.Quotient.eq primeFirstTraceSummableIdeal).2
    rw [← map_sub]
    apply routeRBoundedTraceToPrimeTrace_mem_summableIdeal
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1
    exact Quotient.sound' hab) x

/-- Coefficient-reindexing map from the multiplicative summable corona into the established
additive constitutive Gamma corona. -/
def routeRSummableHadamardToConstitutiveCorona :
    RouteRSummableHadamardCorona →ₗ[ℂ] ConstitutiveGammaCorona where
  toFun := routeRSummableHadamardToConstitutiveCoronaFun
  map_add' x y := by
    induction x using Quotient.inductionOn' with
    | _ a =>
      induction y using Quotient.inductionOn' with
      | _ b => rfl
  map_smul' c x := by
    induction x using Quotient.inductionOn' with
    | _ a => rfl

@[simp]
theorem routeRSummableHadamardToConstitutiveCorona_mk
    (a : RouteRBoundedTraceSequence) :
    routeRSummableHadamardToConstitutiveCorona
        (Quotient.mk'' a : RouteRSummableHadamardCorona) =
      Submodule.Quotient.mk (routeRBoundedTraceToPrimeTrace a) := by
  rfl

/-- No bounded-tail information is lost when passing to the all-prime constitutive corona. -/
theorem routeRSummableHadamardToConstitutiveCorona_injective :
    Function.Injective routeRSummableHadamardToConstitutiveCorona := by
  have hker : ∀ x : RouteRSummableHadamardCorona,
      routeRSummableHadamardToConstitutiveCorona x = 0 → x = 0 := by
    intro x
    induction x using Quotient.inductionOn' with
    | _ a =>
      intro hzero
      rw [routeRSummableHadamardToConstitutiveCorona_mk] at hzero
      have hp : Summable (fun p : Nat.Primes => a (nthPrimeEquiv.symm p)) :=
        (Submodule.Quotient.mk_eq_zero primeFirstTraceSummableIdeal).mp hzero
      have hn : Summable (fun n : ℕ => a n) := by
        have h := nthPrimeEquiv.summable_iff.mpr hp
        convert h using 1
        funext n
        simp
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change Summable (fun n : ℕ => ‖a n‖)
      exact summable_norm_iff.mpr hn
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker (x - y)
  rw [map_sub, hxy, sub_self]

/-- The square-zero harmonic element maps coefficient-for-coefficient to the physical
constitutive Gamma harmonic class. -/
theorem routeRSummableHadamardToConstitutiveCorona_harmonic :
    routeRSummableHadamardToConstitutiveCorona
        (routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence) =
      constitutiveGammaPrimeHarmonicClass := by
  change routeRSummableHadamardToConstitutiveCorona
    (Quotient.mk'' routeRPrimeHarmonicBoundedTraceSequence) = _
  rw [routeRSummableHadamardToConstitutiveCorona_mk]
  apply congrArg Submodule.Quotient.mk
  funext p
  simp [routeRBoundedTraceToPrimeTrace, constitutiveGammaPrimeHarmonicSequence,
    routeRPrimeHarmonicBoundedTraceSequence, routeRPrimeHarmonicTraceSequence]

/-- Unique oriented lift of the physical critical-wall class to the multiplicative corona. -/
def routeRPrimeGammaCriticalWallSummableHadamardClass
    (t : ℝ) : RouteRSummableHadamardCorona :=
  if 0 < t then
    -routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence
  else if t < 0 then
    routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence
  else 0

/-- The oriented multiplicative lift maps exactly to the established physical wall class. -/
theorem routeRSummableHadamardToConstitutiveCorona_criticalWall
    (t : ℝ) :
    routeRSummableHadamardToConstitutiveCorona
        (routeRPrimeGammaCriticalWallSummableHadamardClass t) =
      constitutiveGammaCriticalWallClass t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hnot : ¬ 0 < t := not_lt.mpr ht.le
    rw [routeRPrimeGammaCriticalWallSummableHadamardClass,
      if_neg hnot, if_pos ht,
      routeRSummableHadamardToConstitutiveCorona_harmonic,
      constitutiveGammaCriticalWallClass_eq_harmonic_of_neg ht]
  · have hzero : constitutiveGammaCriticalWallClass 0 = 0 := by
      by_contra h
      exact ((constitutiveGammaCriticalWallClass_ne_zero_iff 0).mp h) rfl
    rw [routeRPrimeGammaCriticalWallSummableHadamardClass,
      if_neg (lt_irrefl 0), if_neg (lt_irrefl 0), map_zero, hzero]
  · rw [routeRPrimeGammaCriticalWallSummableHadamardClass,
      if_pos ht, map_neg,
      routeRSummableHadamardToConstitutiveCorona_harmonic,
      constitutiveGammaCriticalWallClass_eq_neg_harmonic_of_pos ht]

/-- The multiplicative critical-wall lift is nonzero exactly at nonneutral grade. -/
theorem routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff
    (t : ℝ) :
    routeRPrimeGammaCriticalWallSummableHadamardClass t ≠ 0 ↔ t ≠ 0 := by
  constructor
  · intro h ht
    subst t
    exact h (by simp [routeRPrimeGammaCriticalWallSummableHadamardClass])
  · intro ht hzero
    have hmap := congrArg routeRSummableHadamardToConstitutiveCorona hzero
    rw [routeRSummableHadamardToConstitutiveCorona_criticalWall, map_zero] at hmap
    exact ((constitutiveGammaCriticalWallClass_ne_zero_iff t).mpr ht) hmap

/-- Every lifted critical-wall class is square-zero, including the neutral zero class. -/
theorem routeRPrimeGammaCriticalWallSummableHadamardClass_sq_zero
    (t : ℝ) :
    routeRPrimeGammaCriticalWallSummableHadamardClass t ^ 2 = 0 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hnot : ¬ 0 < t := not_lt.mpr ht.le
    rw [routeRPrimeGammaCriticalWallSummableHadamardClass,
      if_neg hnot, if_pos ht,
      routeRPrimeHarmonicSummableHadamardClass_sq_zero]
  · simp [routeRPrimeGammaCriticalWallSummableHadamardClass]
  · rw [routeRPrimeGammaCriticalWallSummableHadamardClass, if_pos ht]
    calc
      (-routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence) ^ 2 =
          routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence ^ 2 := by ring
      _ = 0 := routeRPrimeHarmonicSummableHadamardClass_sq_zero

/-- Reduced multiplicative receivers erase every physical critical-wall lift, including nonzero
off-neutral lifts.  Reduced landing is therefore a blindness theorem, not an annihilation law in
the source corona. -/
theorem routeRPrimeGammaCriticalWallSummableHadamardClass_map_eq_zero
    {S : Type*} [CommRing S] [IsReduced S]
    (phi : RouteRSummableHadamardCorona →+* S) (t : ℝ) :
    phi (routeRPrimeGammaCriticalWallSummableHadamardClass t) = 0 := by
  exact ((show IsNilpotent
      (routeRPrimeGammaCriticalWallSummableHadamardClass t) from
        ⟨2, routeRPrimeGammaCriticalWallSummableHadamardClass_sq_zero t⟩).map phi).eq_zero

/-- At nonneutral grade no map to a reduced ring can be injective on the physical wall lift. -/
theorem routeRPrimeGammaCriticalWall_no_reduced_receiver_injective
    {S : Type*} [CommRing S] [IsReduced S]
    (phi : RouteRSummableHadamardCorona →+* S)
    {t : ℝ} (ht : t ≠ 0) :
    ¬ Function.Injective phi := by
  intro hinj
  have hzero : routeRPrimeGammaCriticalWallSummableHadamardClass t = 0 :=
    hinj (by
      rw [routeRPrimeGammaCriticalWallSummableHadamardClass_map_eq_zero phi t,
        map_zero])
  exact ((routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff t).mpr ht) hzero

/-- Reflection reverses the orientation of the lifted wall defect. -/
theorem routeRPrimeGammaCriticalWallSummableHadamardClass_neg
    (t : ℝ) :
    routeRPrimeGammaCriticalWallSummableHadamardClass (-t) =
      -routeRPrimeGammaCriticalWallSummableHadamardClass t := by
  apply routeRSummableHadamardToConstitutiveCorona_injective
  rw [routeRSummableHadamardToConstitutiveCorona_criticalWall, map_neg,
    routeRSummableHadamardToConstitutiveCorona_criticalWall,
    constitutiveGammaCriticalWallClass_neg]

/-- The physical wall defect is stationary under cofinal deletion of finitely many primes. -/
theorem routeRPrimeGammaCriticalWallSummableHadamardClass_shift_fixed
    (t : ℝ) :
    routeRSummableHadamardShiftEquiv
        (routeRPrimeGammaCriticalWallSummableHadamardClass t) =
      routeRPrimeGammaCriticalWallSummableHadamardClass t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hnot : ¬ 0 < t := not_lt.mpr ht.le
    rw [routeRPrimeGammaCriticalWallSummableHadamardClass,
      if_neg hnot, if_pos ht,
      routeRPrimeHarmonicSummableHadamardClass_shift_fixed]
  · simp [routeRPrimeGammaCriticalWallSummableHadamardClass]
  · rw [routeRPrimeGammaCriticalWallSummableHadamardClass,
      if_pos ht, map_neg,
      routeRPrimeHarmonicSummableHadamardClass_shift_fixed]

end

end RHTower
