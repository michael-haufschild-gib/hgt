import GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.PolarSecondDifference
import GaloisForLFunctions.AdelicKreinGeometry.ASignatureFormulaForPrimeTowers
import GaloisForLFunctions.AdelicKreinGeometry.WeilsArchimedeanStateCountsTheZeros
import GaloisForLFunctions.ArithmeticKreinLangerTheory.FiniteSupportMakesAlmostEveryPrimeDecideZeta
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWeilKernelHasInfinitelyManyPositiveSquares
import Mathlib.Topology.Instances.ENat

/-!
# Inter-tower coupling rigidity and untruncated separable obstructions

Every finite prime set `S` defines a valuation retraction `projS S : posUnits →* posUnits`
(`u ↦ ∏_{p ∈ S} p^{v_p(u)}`). Pulling a dilation kernel `K` back along `projS S` gives the
**coupled `S`-tower assembly** `coupledAssembly S K = K ∘ projS S`, which decomposes canonically as

  `coupledAssembly S K = axialAssembly S K + interTowerCoupling S K`.

* **Exact axial–coupling decomposition and uniqueness** (`coupledAssembly_eq_axial_add_interTower`,
  `axialAssembly_eq_towerAssembly_of_nonempty`, `towerAssembly_eq_axialAssembly_of_agrees`,
  `interTowerCoupling_primeUnit_zpow`): `axialAssembly S K` is the unique separable prime-tower
  assembly matching `K` on all prime powers `p^d` (`p ∈ S`, `d ∈ ℤ`), while `interTowerCoupling S K`
  vanishes identically on `1` and on every single-prime axis `p^ℤ` (`p ∈ S`) yet equals the
  off-axis cross-difference `coprimeCrossDiff K (p^a) (q^b)` on two-prime products.
* **Coprime cross-difference rigidity** (`coprimeCrossDiff_towerAssembly_eq_zero`,
  `negIndex_le_two_of_coprimeCrossDiff_eq_zero`, `exists_coprimeCrossDiff_ratCorr_ne_zero`,
  `not_tendsto_towerAssembly_ratCorr`): every separable prime-tower assembly satisfies
  `coprimeCrossDiff K u v = 0` on disjoint prime supports. For any continuous scale profile
  `K(u) = Φ(log u)`, vanishing of `coprimeCrossDiff` on `⟨2, 3⟩ × ⟨5, 7⟩` forces `Φ(x) = a + b x`
  by Kronecker density of two-prime log-lattices, hence `κ(K) ≤ 2` and `κ₊(K) ≤ 2`. Because
  `ratCorr` is continuous in `log u` and satisfies `κ(ratCorr) = ⊤ ∨ κ₊(ratCorr) = ⊤`
  unconditionally, `ratCorr` has nonzero coprime cross-differences on `⟨2, 3⟩ × ⟨5, 7⟩` and no
  nontrivial net of arbitrary separable prime-tower assemblies converges pointwise to `ratCorr`.
* **Untruncated axial replication blow-up** (`negIndex_archGlue_axialAssembly_ratCorr_ge`,
  `tendsto_negIndex_archGlue_axialAssembly_ratCorr_atTop`): on the non-RH finite stratum
  `0 < κ(K_ζ) < ⊤`, every non-blind prime `p ∉ zetaBlindPrimes` contributes local polar index
  `κ₀ ≥ κ(K_ζ) - 1 ≥ 1`, so `κ(archGlue(axialAssembly S ratCorr, c)) → ⊤` along `atTop`.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate Real Classical
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx cx_contDiff cx_hasCompactSupport
  rightZeros)
open GaloisForLFunctions.ArithmeticKreinLangerTheory (zetaBlindPrimes
  zetaBlindPrimes_finite_card_le negIndex_zetaKernel_prime_eq)
open GaloisForLFunctions.RenormalizedIntersectionTheory (posIndex_zetaKernel_eq_top_of_finite)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling

/-! ### The `S`-valuation section and retraction on `ℚ_{>0}` -/

theorem primeUnit_eq_primePos (p : Nat.Primes) :
    primeUnit p = @primePos (p : ℕ) ⟨p.2⟩ := rfl

theorem posUnitsToHecke_primeUnit (p : Nat.Primes) :
    posUnitsToHecke (primeUnit p) = primeElt p.2 :=
  Subtype.ext rfl

theorem logPos_mul (u v : posUnits) : logPos (u * v) = logPos u + logPos v := by
  have hu : (0 : ℝ) < (((u : ℚˣ) : ℚ) : ℝ) := posUnits_val_pos u
  have hv : (0 : ℝ) < (((v : ℚˣ) : ℚ) : ℝ) := posUnits_val_pos v
  simp only [logPos, Subgroup.coe_mul, Units.val_mul]
  push_cast
  exact Real.log_mul hu.ne' hv.ne'

theorem logPos_one : logPos 1 = 0 := by
  simp [logPos]

theorem logPos_zpow (u : posUnits) (n : ℤ) : logPos (u ^ n) = (n : ℝ) * logPos u := by
  simp only [logPos, Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val]
  push_cast
  exact Real.log_zpow _ n

theorem logPos_primeUnit (p : Nat.Primes) : logPos (primeUnit p) = Real.log (p : ℕ) := by
  simp [logPos, primeUnit]

/-- Multiplicative section `(S → Multiplicative ℤ) →* posUnits` sending `e ↦ ∏_{p ∈ S} p^{e_p}`. -/
def sectionS (S : Finset Nat.Primes) : (S → Multiplicative ℤ) →* posUnits where
  toFun e := ∏ p : S, primeUnit (p : Nat.Primes) ^ Multiplicative.toAdd (e p)
  map_one' := by simp
  map_mul' e₁ e₂ := by simp only [Pi.mul_apply, toAdd_mul, zpow_add, prod_mul_distrib]

theorem valS_sectionS (S : Finset Nat.Primes) (e : S → Multiplicative ℤ) :
    valS S (sectionS S e) = e := by
  funext q
  change towerVal ((q : Nat.Primes) : ℕ) (sectionS S e) = e q
  simp only [sectionS, MonoidHom.coe_mk, OneHom.coe_mk, map_prod]
  rw [Finset.prod_eq_single q]
  · rw [map_zpow, primeUnit_eq_primePos, towerVal_primePos, if_pos rfl, ← ofAdd_zsmul,
      smul_eq_mul, mul_one, ofAdd_toAdd]
  · intro p _ hpq
    rw [map_zpow, primeUnit_eq_primePos, towerVal_primePos,
      if_neg (fun h => hpq (Subtype.ext h)), ofAdd_zero, one_zpow]
  · intro h; exact absurd (mem_univ q) h

/-- The `S`-valuation retraction `u ↦ ∏_{p ∈ S} p^{v_p(u)}` on `ℚ_{>0}`. -/
def projS (S : Finset Nat.Primes) : posUnits →* posUnits :=
  (sectionS S).comp (valS S)

theorem valS_projS (S : Finset Nat.Primes) (u : posUnits) :
    valS S (projS S u) = valS S u :=
  valS_sectionS S (valS S u)

theorem projS_idem (S : Finset Nat.Primes) (u : posUnits) :
    projS S (projS S u) = projS S u := by
  simp only [projS, MonoidHom.comp_apply, valS_sectionS]

theorem projS_eq_self_of_primeSupp_subset {S : Finset Nat.Primes} {u : posUnits}
    (hu : primeSupp ((u : ℚˣ) : ℚ) ⊆ S) : projS S u = u := by
  apply Subtype.ext; apply Units.ext
  let φ : posUnits →* ℚ := (Units.coeHom ℚ).comp posUnits.subtype
  have hval : φ (projS S u) = ∏ p ∈ S, ((p : ℕ) : ℚ) ^ padicValRat p ((u : ℚˣ) : ℚ) := by
    simp only [projS, sectionS, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      valS_apply, toAdd_ofAdd, map_prod]
    rw [← S.prod_coe_sort fun p => ((p : ℕ) : ℚ) ^ padicValRat (p : ℕ) ((u : ℚˣ) : ℚ)]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, Units.coeHom_apply,
      Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, primeUnit, Units.val_mk0]
  exact hval.trans (prod_zpow_padicValRat u.2 hu)

theorem projS_primeUnit_zpow {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∈ S) (d : ℤ) :
    projS S (primeUnit p ^ d) = primeUnit p ^ d := by
  have heq : primeUnit p ^ d =
      sectionS S (fun q : S => if (q : Nat.Primes) = p then Multiplicative.ofAdd d else 1) := by
    simp only [sectionS, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Finset.prod_eq_single ⟨p, hp⟩]
    · simp
    · intro q _ hqp
      have hne : (q : Nat.Primes) ≠ p := fun h => hqp (Subtype.ext h)
      simp [hne]
    · intro h; exact absurd (mem_univ _) h
  rw [heq, projS, MonoidHom.comp_apply, valS_sectionS]

theorem projS_periodic (S : Finset Nat.Primes) :
    ∃ v₀ : posUnits, v₀ ≠ 1 ∧ ∀ u, projS S (v₀ * u) = projS S u := by
  classical
  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (S.sup (fun p => (p : ℕ)) + 1)
  have hqS : (⟨q, hq⟩ : Nat.Primes) ∉ S := fun h => by
    have := Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) h
    simp only at this; omega
  refine ⟨primeUnit ⟨q, hq⟩, fun h => ?_, fun u => ?_⟩
  · have := congrArg (fun v : posUnits => (((v : ℚˣ) : ℚ))) h
    simp only [primeUnit, Units.val_mk0, OneMemClass.coe_one, Units.val_one] at this
    exact hq.one_lt.ne' (by exact_mod_cast this)
  · have hv : valS S (primeUnit ⟨q, hq⟩) = 1 := by
      funext p
      change towerVal ((p : Nat.Primes) : ℕ) (primeUnit ⟨q, hq⟩) = 1
      rw [primeUnit_eq_primePos]
      have h := towerVal_primePos ⟨q, hq⟩ (p : Nat.Primes)
      have hne : ¬ ((⟨q, hq⟩ : Nat.Primes) = (p : Nat.Primes)) :=
        fun e => hqS (by rw [e]; exact p.2)
      split_ifs at h with h'
      · exact absurd h' hne
      · rw [h, ofAdd_zero]
    rw [projS, MonoidHom.comp_apply, MonoidHom.comp_apply, map_mul, hv, one_mul]

/-! ### Coupled, axial, and inter-tower coupling kernels -/

/-- The **coupled `S`-tower assembly** `K(∏_{p ∈ S} p^{v_p(u)})` on `ℚ_{>0}`. -/
def coupledAssembly (S : Finset Nat.Primes) (K : posUnits → ℂ) : posUnits → ℂ :=
  K ∘ projS S

/-- The **axial `S`-tower assembly**: the canonical additive sum of the single-prime axis
restrictions of `K`, normalized to agree with `K` at `1`. -/
def axialAssembly (S : Finset Nat.Primes) (K : posUnits → ℂ) (u : posUnits) : ℂ :=
  towerAssembly S (fun p m => K (primeUnit (p : Nat.Primes) ^ Multiplicative.toAdd m) - K 1) u +
    K 1

/-- The **inter-tower coupling kernel**: the pure multi-prime interaction residual of `K` on `S`. -/
def interTowerCoupling (S : Finset Nat.Primes) (K : posUnits → ℂ) (u : posUnits) : ℂ :=
  coupledAssembly S K u - axialAssembly S K u

/-- **Exact axial–coupling decomposition** of the coupled `S`-tower assembly. -/
theorem coupledAssembly_eq_axial_add_interTower (S : Finset Nat.Primes) (K : posUnits → ℂ)
    (u : posUnits) :
    coupledAssembly S K u = axialAssembly S K u + interTowerCoupling S K u := by
  simp [interTowerCoupling]

theorem isHermKernel_coupledAssembly (S : Finset Nat.Primes) {K : posUnits → ℂ}
    (hK : IsHermKernel K) : IsHermKernel (coupledAssembly S K) :=
  hK.comp (projS S)

/-- When `S` is nonempty, `axialAssembly S K` is a genuine separable `towerAssembly` on `S`. -/
theorem axialAssembly_eq_towerAssembly_of_nonempty {S : Finset Nat.Primes} {p₀ : Nat.Primes}
    (hp₀ : p₀ ∈ S) (K : posUnits → ℂ) :
    axialAssembly S K = towerAssembly S fun p m =>
      K (primeUnit (p : Nat.Primes) ^ Multiplicative.toAdd m) -
        if (p : Nat.Primes) = p₀ then 0 else K 1 := by
  classical
  funext u
  simp only [axialAssembly, towerAssembly, Function.comp_apply, separable]
  have hsplit : ∀ p : S,
      (K (primeUnit (p : Nat.Primes) ^ Multiplicative.toAdd (valS S u p)) -
        if (p : Nat.Primes) = p₀ then 0 else K 1) =
      (K (primeUnit (p : Nat.Primes) ^ Multiplicative.toAdd (valS S u p)) - K 1) +
        if p = ⟨p₀, hp₀⟩ then K 1 else 0 := fun p => by
    have heq : ((p : Nat.Primes) = p₀) ↔ p = ⟨p₀, hp₀⟩ :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [heq]
    split_ifs <;> ring
  simp_rw [hsplit, sum_add_distrib, Finset.sum_ite_eq', if_pos (mem_univ _)]

theorem axialAssembly_one (S : Finset Nat.Primes) (K : posUnits → ℂ) :
    axialAssembly S K 1 = K 1 := by
  simp [axialAssembly, towerAssembly, separable]

theorem valS_primeUnit_zpow (S : Finset Nat.Primes) {p : Nat.Primes} (hp : p ∈ S) (d : ℤ)
    (q : S) :
    valS S (primeUnit p ^ d) q =
      if q = ⟨p, hp⟩ then Multiplicative.ofAdd d else 1 := by
  change towerVal ((q : Nat.Primes) : ℕ) (primeUnit p ^ d) = _
  rw [map_zpow, primeUnit_eq_primePos, towerVal_primePos]
  by_cases h : p = (q : Nat.Primes)
  · have hq : q = ⟨p, hp⟩ := Subtype.ext h.symm
    rw [if_pos h, if_pos hq, ← ofAdd_zsmul, smul_eq_mul, mul_one]
  · have hq : q ≠ ⟨p, hp⟩ := fun e => h (congrArg Subtype.val e).symm
    rw [if_neg h, if_neg hq, ofAdd_zero, one_zpow]

/-- `axialAssembly S K` matches `K` on every prime power `p^d` (`p ∈ S`, `d ∈ ℤ`). -/
theorem axialAssembly_primeUnit_zpow {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∈ S)
    (K : posUnits → ℂ) (d : ℤ) :
    axialAssembly S K (primeUnit p ^ d) = K (primeUnit p ^ d) := by
  classical
  simp only [axialAssembly, towerAssembly, Function.comp_apply, separable]
  rw [Finset.sum_eq_single ⟨p, hp⟩]
  · rw [valS_primeUnit_zpow S hp d ⟨p, hp⟩, if_pos rfl, toAdd_ofAdd]; ring
  · intro q _ hqp
    rw [valS_primeUnit_zpow S hp d q, if_neg hqp, toAdd_one, zpow_zero, sub_self]
  · intro h; exact absurd (mem_univ _) h

/-- **Uniqueness of the axial assembly.** Any separable prime-tower assembly on nonempty `S` that
matches `K` on all prime powers `p^d` (`p ∈ S`, `d ∈ ℤ`) is equal to `axialAssembly S K`. -/
theorem towerAssembly_eq_axialAssembly_of_agrees {S : Finset Nat.Primes} (hS : S.Nonempty)
    {K : posUnits → ℂ} {k : S → Multiplicative ℤ → ℂ}
    (hagree : ∀ p ∈ S, ∀ d : ℤ, towerAssembly S k (primeUnit p ^ d) = K (primeUnit p ^ d)) :
    towerAssembly S k = axialAssembly S K := by
  classical
  obtain ⟨p₀, hp₀⟩ := hS
  have h1 : ∑ q : S, k q 1 = K 1 := by
    have h0 := hagree p₀ hp₀ 0
    simpa [towerAssembly, separable] using h0
  have haxis : ∀ (p : S) (m : Multiplicative ℤ),
      k p m - k p 1 = K (primeUnit (p : Nat.Primes) ^ Multiplicative.toAdd m) - K 1 := by
    intro p m
    have hd := hagree (p : Nat.Primes) p.2 (Multiplicative.toAdd m)
    simp only [towerAssembly, Function.comp_apply, separable] at hd
    have hsum : ∑ q : S, k q (valS S (primeUnit (p : Nat.Primes) ^ Multiplicative.toAdd m) q) =
        k p m + ∑ q ∈ univ.erase p, k q 1 := by
      rw [← add_sum_erase univ _ (mem_univ p)]
      congr 1
      · rw [valS_primeUnit_zpow S p.2 (Multiplicative.toAdd m) p, if_pos rfl, ofAdd_toAdd]
      · refine sum_congr rfl fun q hq => ?_
        rw [valS_primeUnit_zpow S p.2 (Multiplicative.toAdd m) q,
          if_neg (mem_erase.mp hq).1]
    have hsum1 : ∑ q : S, k q 1 = k p 1 + ∑ q ∈ univ.erase p, k q 1 :=
      (add_sum_erase univ _ (mem_univ p)).symm
    rw [hsum] at hd
    linear_combination hd - h1 + hsum1
  funext u
  simp only [axialAssembly, towerAssembly, Function.comp_apply, separable, ← haxis]
  rw [sum_sub_distrib, h1, sub_add_cancel]

/-- The inter-tower coupling vanishes at the identity. -/
theorem interTowerCoupling_one (S : Finset Nat.Primes) (K : posUnits → ℂ) :
    interTowerCoupling S K 1 = 0 := by
  simp [interTowerCoupling, coupledAssembly, axialAssembly_one]

/-- The inter-tower coupling vanishes identically on every single-prime axis `p^ℤ` (`p ∈ S`). -/
theorem interTowerCoupling_primeUnit_zpow {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∈ S)
    (K : posUnits → ℂ) (d : ℤ) :
    interTowerCoupling S K (primeUnit p ^ d) = 0 := by
  rw [interTowerCoupling, coupledAssembly, Function.comp_apply, projS_primeUnit_zpow hp d,
    axialAssembly_primeUnit_zpow hp K d, sub_self]

/-! ### The coprime cross-difference invariant and continuous log-additivity rigidity -/

/-- The multiplicative second difference `K(u v) - K(u) - K(v) + K(1)`. -/
def coprimeCrossDiff (K : posUnits → ℂ) (u v : posUnits) : ℂ :=
  K (u * v) - K u - K v + K 1

/-- On products of two distinct prime powers in `S`, the inter-tower coupling equals the coprime
cross-difference. -/
theorem interTowerCoupling_mul_primeUnit {S : Finset Nat.Primes} {p q : Nat.Primes}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) (K : posUnits → ℂ) (a b : ℤ) :
    interTowerCoupling S K (primeUnit p ^ a * primeUnit q ^ b) =
      coprimeCrossDiff K (primeUnit p ^ a) (primeUnit q ^ b) := by
  classical
  have hproj : projS S (primeUnit p ^ a * primeUnit q ^ b) =
      primeUnit p ^ a * primeUnit q ^ b := by
    rw [map_mul, projS_primeUnit_zpow hp, projS_primeUnit_zpow hq]
  have hax : axialAssembly S K (primeUnit p ^ a * primeUnit q ^ b) =
      K (primeUnit p ^ a) + K (primeUnit q ^ b) - K 1 := by
    let pS : S := ⟨p, hp⟩
    let qS : S := ⟨q, hq⟩
    simp only [axialAssembly, towerAssembly, Function.comp_apply, separable, map_mul, Pi.mul_apply]
    have hne : pS ≠ qS := fun h => hpq (congrArg Subtype.val h)
    rw [← add_sum_erase univ _ (mem_univ pS),
      ← add_sum_erase (univ.erase pS) _ (mem_erase.mpr ⟨hne.symm, mem_univ qS⟩)]
    have hp_val : valS S (primeUnit p ^ a) pS * valS S (primeUnit q ^ b) pS =
        Multiplicative.ofAdd a := by
      rw [valS_primeUnit_zpow S hp a pS, if_pos rfl,
        valS_primeUnit_zpow S hq b pS, if_neg hne, mul_one]
    have hq_val : valS S (primeUnit p ^ a) qS * valS S (primeUnit q ^ b) qS =
        Multiplicative.ofAdd b := by
      rw [valS_primeUnit_zpow S hp a qS, if_neg hne.symm,
        valS_primeUnit_zpow S hq b qS, if_pos rfl, one_mul]
    have hrest : ∑ r ∈ (univ.erase pS).erase qS,
        (K (primeUnit (r : Nat.Primes) ^ Multiplicative.toAdd
          (valS S (primeUnit p ^ a) r * valS S (primeUnit q ^ b) r)) - K 1) = 0 := by
      refine sum_eq_zero fun r hr => ?_
      have hrq : r ≠ qS := (mem_erase.mp hr).1
      have hrp : r ≠ pS := (mem_erase.mp (mem_erase.mp hr).2).1
      rw [valS_primeUnit_zpow S hp a r, if_neg hrp, valS_primeUnit_zpow S hq b r, if_neg hrq,
        one_mul, toAdd_one, zpow_zero, sub_self]
    rw [hp_val, hq_val, hrest, toAdd_ofAdd, toAdd_ofAdd]
    simp only [pS, qS]
    ring
  rw [interTowerCoupling, coupledAssembly, Function.comp_apply, hproj, hax, coprimeCrossDiff]
  ring

/-- **Separable vanishing of coprime cross-differences.** Every separable prime-tower assembly
annihilates `coprimeCrossDiff` on pairs `(u, v)` with disjoint `S`-valuations. -/
theorem coprimeCrossDiff_towerAssembly_eq_zero (S : Finset Nat.Primes)
    (k : S → Multiplicative ℤ → ℂ) {u v : posUnits}
    (hdisj : ∀ p : S, valS S u p = 1 ∨ valS S v p = 1) :
    coprimeCrossDiff (towerAssembly S k) u v = 0 := by
  simp only [coprimeCrossDiff, towerAssembly, Function.comp_apply, map_mul, map_one, separable]
  have hterm : ∀ p : S,
      k p (valS S u p * valS S v p) - k p (valS S u p) - k p (valS S v p) + k p 1 = 0 := by
    intro p
    rcases hdisj p with hu | hv
    · rw [hu, one_mul]; ring
    · rw [hv, mul_one]; ring
  have hsum : ∑ p : S,
      (k p (valS S u p * valS S v p) - k p (valS S u p) - k p (valS S v p) + k p 1) = 0 :=
    sum_eq_zero fun p _ => hterm p
  simp only [sum_add_distrib, sum_sub_distrib] at hsum
  exact hsum

/-- Rank-two subgroup of `posUnits` generated by two primes. -/
def twoPrimeUnits (p q : Nat.Primes) : Subgroup posUnits :=
  Subgroup.closure {primeUnit p, primeUnit q}

theorem towerVal_eq_one_of_mem_twoPrimeUnits {p q r : Nat.Primes} (hrp : r ≠ p) (hrq : r ≠ q)
    {u : posUnits} (hu : u ∈ twoPrimeUnits p q) :
    @towerVal (r : ℕ) ⟨r.2⟩ u = 1 := by
  haveI : Fact (r : ℕ).Prime := ⟨r.2⟩
  unfold twoPrimeUnits at hu
  induction hu using Subgroup.closure_induction with
  | mem v hv =>
    rcases Set.mem_insert_iff.mp hv with rfl | hv'
    · rw [primeUnit_eq_primePos, towerVal_primePos, if_neg hrp.symm, ofAdd_zero]
    · rw [Set.mem_singleton_iff.mp hv', primeUnit_eq_primePos, towerVal_primePos,
        if_neg hrq.symm, ofAdd_zero]
  | one => exact map_one _
  | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]
  | inv x _ hx => rw [map_inv, hx, inv_one]

/-- On two disjoint prime pairs, EVERY separable prime-tower assembly (for every `S` and `k`) has
identically zero `coprimeCrossDiff`. -/
theorem coprimeCrossDiff_towerAssembly_twoPrimeUnits {p q r s : Nat.Primes}
    (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s)
    (S : Finset Nat.Primes) (k : S → Multiplicative ℤ → ℂ)
    {u v : posUnits} (hu : u ∈ twoPrimeUnits p q) (hv : v ∈ twoPrimeUnits r s) :
    coprimeCrossDiff (towerAssembly S k) u v = 0 := by
  refine coprimeCrossDiff_towerAssembly_eq_zero S k fun t => ?_
  by_cases htpq : (t : Nat.Primes) = p ∨ (t : Nat.Primes) = q
  · right
    rcases htpq with htp | htq
    · exact towerVal_eq_one_of_mem_twoPrimeUnits (htp ▸ hpr) (htp ▸ hps) hv
    · exact towerVal_eq_one_of_mem_twoPrimeUnits (htq ▸ hqr) (htq ▸ hqs) hv
  · left
    push Not at htpq
    exact towerVal_eq_one_of_mem_twoPrimeUnits htpq.1 htpq.2 hu

theorem dense_range_logPos_twoPrimeUnits {p q : Nat.Primes} (hpq : p ≠ q) :
    Dense (Set.range fun u : twoPrimeUnits p q => logPos u) := by
  have hpq_nat : (p : ℕ) ≠ (q : ℕ) := fun h => hpq (Subtype.ext h)
  have hdense : Dense (AddSubgroup.closure {Real.log (p : ℕ), Real.log (q : ℕ)} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (RHTower.irrational_log_ratio q.2 p.2 hpq_nat.symm)
  refine hdense.mono fun x hx => ?_
  obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hx
  refine ⟨⟨primeUnit p ^ m * primeUnit q ^ n, Subgroup.mem_closure_pair.mpr ⟨m, n, rfl⟩⟩, ?_⟩
  change logPos (primeUnit p ^ m * primeUnit q ^ n) = x
  rw [logPos_mul, logPos_zpow, logPos_zpow, logPos_primeUnit, logPos_primeUnit, ← hmn,
    zsmul_eq_mul, zsmul_eq_mul]

/-- Cauchy's functional equation on `ℝ` for continuous `ℂ`-valued functions. -/
private theorem eq_mul_of_add_of_continuous {ψ : ℝ → ℂ} (hcont : Continuous ψ)
    (hadd : ∀ x y : ℝ, ψ (x + y) = ψ x + ψ y) (x : ℝ) :
    ψ x = (x : ℂ) * ψ 1 := by
  let Ψ : ℝ →+ ℂ := AddMonoidHom.mk' ψ hadd
  have hnat : ∀ n : ℕ, ψ (n : ℝ) = (n : ℂ) * ψ 1 := fun n => by
    have h := map_nsmul Ψ n (1 : ℝ)
    simpa [Ψ, nsmul_eq_mul] using h
  have hint : ∀ z : ℤ, ψ (z : ℝ) = (z : ℂ) * ψ 1 := fun z => by
    have h := map_zsmul Ψ z (1 : ℝ)
    simpa [Ψ, zsmul_eq_mul] using h
  have hrat : ∀ q : ℚ, ψ (q : ℝ) = ((q : ℝ) : ℂ) * ψ 1 := fun q => by
    have hden_ne : (q.den : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    have hden_r : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    have hmul : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
      rw [Rat.cast_def, mul_div_cancel₀ _ hden_r]
    have h1 : (q.den : ℂ) * ψ (q : ℝ) = ψ (q.num : ℝ) := by
      have := map_nsmul Ψ q.den (q : ℝ)
      simp only [Ψ, AddMonoidHom.mk'_apply, nsmul_eq_mul, hmul] at this
      exact this.symm
    have h2 : ψ (q : ℝ) = ψ (q.num : ℝ) / (q.den : ℂ) :=
      (eq_div_iff hden_ne).mpr (by linear_combination h1)
    rw [h2, hint q.num, Rat.cast_def]
    push_cast
    ring
  have hcl : IsClosed {y : ℝ | ψ y = (y : ℂ) * ψ 1} :=
    isClosed_eq hcont (Complex.continuous_ofReal.mul continuous_const)
  have hsub : Set.range (Rat.cast : ℚ → ℝ) ⊆ {y : ℝ | ψ y = (y : ℂ) * ψ 1} := by
    rintro _ ⟨q, rfl⟩; exact hrat q
  exact (hcl.closure_subset_iff.mpr hsub) (Rat.denseRange_cast x)

/-- Log-moment linear functional `w ↦ Σ_i w_i log u_i`. -/
private def logMass {n : ℕ} (x : Fin n → posUnits) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun w := ∑ i, w i * (logPos (x i) : ℂ)
  map_add' w₁ w₂ := by simp [add_mul, sum_add_distrib]
  map_smul' t w := by simp [mul_assoc, mul_sum]

/-- An affine-in-`logPos` kernel `u ↦ a + b log u` has at most two negative and two positive
squares. -/
theorem negIndex_and_posIndex_affine_logPos_le_two (a b : ℂ) :
    negIndex (fun u : posUnits => a + b * (logPos u : ℂ)) ≤ 2 ∧
      RenormalizedIntersectionTheory.posIndex (fun u : posUnits => a + b * (logPos u : ℂ)) ≤ 2 := by
  have hbound : ∀ (a' b' : ℂ), negIndex (fun u : posUnits => a' + b' * (logPos u : ℂ)) ≤ 2 := by
    intro a' b'
    refine negIndex_le_iff.mpr fun n x => ?_
    set F : Fin 2 → (Fin n → ℂ) →ₗ[ℂ] ℂ := ![totalMass (Fin n), logMass x]
    have hvan : ∀ c : Fin n → ℂ, (∀ j, c ∈ LinearMap.ker (F j)) →
        0 ≤ hermQuad (gram (fun u : posUnits => a' + b' * (logPos u : ℂ)) x) c := by
      intro c hc
      have hc0 : ∑ i, c i = 0 := hc 0
      have hc1 : ∑ i, c i * (logPos (x i) : ℂ) = 0 := hc 1
      rw [hermQuad_gram]
      have hzero : (∑ i : Fin n, ∑ j : Fin n,
          conj (c i) * (a' + b' * (logPos ((x i)⁻¹ * x j) : ℂ)) * c j) = 0 := by
        have hstep : ∀ i j : Fin n,
            conj (c i) * (a' + b' * (logPos ((x i)⁻¹ * x j) : ℂ)) * c j =
              a' * conj (c i) * c j + b' * conj (c i) * (c j * (logPos (x j) : ℂ)) -
                b' * (conj (c i) * (logPos (x i) : ℂ)) * c j := fun i j => by
          rw [logPos_inv_mul]; push_cast; ring
        simp_rw [hstep, sum_sub_distrib, sum_add_distrib]
        have hs1 : ∑ i : Fin n, ∑ j : Fin n, a' * conj (c i) * c j =
            (∑ i : Fin n, a' * conj (c i)) * ∑ j : Fin n, c j := by
          rw [Finset.sum_mul]; exact sum_congr rfl fun i _ => (mul_sum _ _ _).symm
        have hs2 : ∑ i : Fin n, ∑ j : Fin n, b' * conj (c i) * (c j * (logPos (x j) : ℂ)) =
            (∑ i : Fin n, b' * conj (c i)) * ∑ j : Fin n, c j * (logPos (x j) : ℂ) := by
          rw [Finset.sum_mul]; exact sum_congr rfl fun i _ => (mul_sum _ _ _).symm
        have hs3 : ∑ i : Fin n, ∑ j : Fin n, b' * (conj (c i) * (logPos (x i) : ℂ)) * c j =
            (∑ i : Fin n, b' * (conj (c i) * (logPos (x i) : ℂ))) * ∑ j : Fin n, c j := by
          rw [Finset.sum_mul]; exact sum_congr rfl fun i _ => (mul_sum _ _ _).symm
        rw [hs1, hs2, hs3, hc0, hc1]; ring
      rw [hzero, Complex.zero_re]
    have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _ F hvan
    rw [Fintype.card_fin] at h
    exact Nat.cast_le.mpr h
  refine ⟨hbound a b, ?_⟩
  have heq : (fun u : posUnits => -(a + b * (logPos u : ℂ))) =
      fun u : posUnits => -a + (-b) * (logPos u : ℂ) := funext fun _ => by ring
  rw [RenormalizedIntersectionTheory.posIndex, heq]
  exact hbound (-a) (-b)

/-- **Continuous log-additivity rigidity.** If `K(u) = Φ(log u)` has continuous profile `Φ` and
vanishing `coprimeCrossDiff` on two disjoint rank-two prime lattices, then `Φ` is affine on `ℝ` and
both `κ(K) ≤ 2` and `κ₊(K) ≤ 2`. -/
theorem negIndex_le_two_of_coprimeCrossDiff_eq_zero {Φ : ℝ → ℂ} (hΦ : Continuous Φ)
    {p q r s : Nat.Primes} (hpq : p ≠ q) (hrs : r ≠ s)
    (hvan : ∀ u ∈ twoPrimeUnits p q, ∀ v ∈ twoPrimeUnits r s,
      coprimeCrossDiff (fun w => Φ (logPos w)) u v = 0) :
    (∀ x : ℝ, Φ x = Φ 0 + (x : ℂ) * (Φ 1 - Φ 0)) ∧
      negIndex (fun w : posUnits => Φ (logPos w)) ≤ 2 ∧
      RenormalizedIntersectionTheory.posIndex (fun w : posUnits => Φ (logPos w)) ≤ 2 := by
  have hd1 := dense_range_logPos_twoPrimeUnits hpq
  have hd2 := dense_range_logPos_twoPrimeUnits hrs
  have hd_prod : Dense (Set.range fun uv : twoPrimeUnits p q × twoPrimeUnits r s =>
      (logPos uv.1, logPos uv.2)) := by
    have heq : (Set.range fun uv : twoPrimeUnits p q × twoPrimeUnits r s =>
        (logPos uv.1, logPos uv.2)) =
        (Set.range fun u : twoPrimeUnits p q => logPos u) ×ˢ
          (Set.range fun v : twoPrimeUnits r s => logPos v) := by
      ext ⟨x, y⟩; simp [Set.mem_prod]
    rw [heq]
    exact hd1.prod hd2
  set F : ℝ × ℝ → ℂ := fun xy => Φ (xy.1 + xy.2) - Φ xy.1 - Φ xy.2 + Φ 0
  have hFc : Continuous F := by fun_prop
  have hF_zero_on : ∀ uv : twoPrimeUnits p q × twoPrimeUnits r s,
      F (logPos uv.1, logPos uv.2) = 0 := fun ⟨u, v⟩ => by
    have h := hvan u u.2 v v.2
    simpa [F, coprimeCrossDiff, logPos_mul, logPos_one] using h
  have hF_eq : ∀ xy : ℝ × ℝ, F xy = 0 := fun xy => by
    have hcl : IsClosed {z : ℝ × ℝ | F z = 0} := isClosed_eq hFc continuous_const
    have hsub : (Set.range fun uv : twoPrimeUnits p q × twoPrimeUnits r s =>
        (logPos uv.1, logPos uv.2)) ⊆ {z : ℝ × ℝ | F z = 0} := by
      rintro _ ⟨uv, rfl⟩; exact hF_zero_on uv
    exact (hcl.closure_subset_iff.mpr hsub) (hd_prod xy)
  set ψ : ℝ → ℂ := fun x => Φ x - Φ 0
  have hψc : Continuous ψ := hΦ.sub continuous_const
  have hψ_add : ∀ x y : ℝ, ψ (x + y) = ψ x + ψ y := fun x y => by
    have hxy : F (x, y) = 0 := hF_eq (x, y)
    simp only [F, ψ] at hxy ⊢
    linear_combination hxy
  have haff : ∀ x : ℝ, Φ x = Φ 0 + (x : ℂ) * (Φ 1 - Φ 0) := fun x => by
    have hx := eq_mul_of_add_of_continuous hψc hψ_add x
    simp only [ψ] at hx
    linear_combination hx
  have heq : (fun w : posUnits => Φ (logPos w)) =
      fun w : posUnits => Φ 0 + (Φ 1 - Φ 0) * (logPos w : ℂ) :=
    funext fun w => by rw [haff (logPos w)]; ring
  rw [heq]
  exact ⟨haff, negIndex_and_posIndex_affine_logPos_le_two (Φ 0) (Φ 1 - Φ 0)⟩

/-! ### Unconditional non-separability of Weil's correlation `ratCorr` -/

theorem weilTest_translate_eq_transl (y : ℝ) (g : ℝ → ℂ) :
    EF.weilTest (ArithmeticCastelnuovoSeveri.translate y g) g =
      RHTower.WeilSpectral.transl y (EF.weilTest g g) := by
  funext x
  have h := ArithmeticCastelnuovoSeveri.weilTest_translate y 0 g g x
  have h0 : ArithmeticCastelnuovoSeveri.translate 0 g = g := by
    funext t; simp [ArithmeticCastelnuovoSeveri.translate]
  rw [h0, sub_zero] at h
  exact h

/-- Continuity of the cubic-spline Weil correlation `splineCorr` on `ℝ`. -/
theorem continuous_splineCorr : Continuous splineCorr := by
  have heq : splineCorr = fun y => RHTower.weilFullFunctional vonMangoldtWeight
      (RHTower.WeilSpectral.transl y (EF.weilTest (cx cubicSpline) (cx cubicSpline))) :=
    funext fun y => by rw [splineCorr, weilTest_translate_eq_transl]
  rw [heq]
  exact RHTower.WeilSpectral.continuous_spectralKernel vonMangoldtWeight
    (RHTower.WeilSpectral.admissible_weilTest (cx_contDiff contDiff_cubicSpline)
      (cx_hasCompactSupport hasCompactSupport_cubicSpline))

theorem posIndex_ratCorr :
    RenormalizedIntersectionTheory.posIndex ratCorr =
      RenormalizedIntersectionTheory.posIndex zetaKernel := by
  have heq : (fun u : posUnits => -ratCorr u) = (fun x => -zetaKernel x) ∘ posUnitsToHecke :=
    funext fun u => by simp [ratCorr_eq_zetaKernel]
  rw [RenormalizedIntersectionTheory.posIndex, RenormalizedIntersectionTheory.posIndex, heq,
    negIndex_comp_of_surjective _ _ posUnitsToHecke_surjective]

/-- **Unconditional infinite total inertia of `ratCorr`.** Either `κ(ratCorr) = ⊤` (infinitely many
off-line zeros) or `κ₊(ratCorr) = ⊤` (finitely many off-line zeros, where infinitely many critical
zeros are seen by the cubic spline). -/
theorem negIndex_or_posIndex_ratCorr_eq_top :
    negIndex ratCorr = ⊤ ∨ RenormalizedIntersectionTheory.posIndex ratCorr = ⊤ := by
  rcases (rightZeros zetaZeroConfig).finite_or_infinite with hfin | hinf
  · right
    rw [posIndex_ratCorr]
    exact posIndex_zetaKernel_eq_top_of_finite hfin
  · left
    rw [negIndex_ratCorr, negIndex_zetaKernel]
    exact Set.encard_eq_top_iff.mpr hinf

private theorem prime_ne {p q : Nat.Primes} (h : (p : ℕ) ≠ (q : ℕ)) : p ≠ q :=
  fun e => h (congrArg Subtype.val e)

def prime2 : Nat.Primes := ⟨2, Nat.prime_two⟩
def prime3 : Nat.Primes := ⟨3, Nat.prime_three⟩
def prime5 : Nat.Primes := ⟨5, by norm_num⟩
def prime7 : Nat.Primes := ⟨7, by norm_num⟩

/-- **Unconditional nonvanishing of inter-tower coupling in `ratCorr`.** There exist `u ∈ ⟨2, 3⟩`
and `v ∈ ⟨5, 7⟩` with `coprimeCrossDiff ratCorr u v ≠ 0`. -/
theorem exists_coprimeCrossDiff_ratCorr_ne_zero :
    ∃ u ∈ twoPrimeUnits prime2 prime3, ∃ v ∈ twoPrimeUnits prime5 prime7,
      coprimeCrossDiff ratCorr u v ≠ 0 := by
  by_contra hall
  push Not at hall
  have hpq : prime2 ≠ prime3 := prime_ne (by norm_num [prime2, prime3])
  have hrs : prime5 ≠ prime7 := prime_ne (by norm_num [prime5, prime7])
  have hΦ : Continuous fun x : ℝ => splineCorr (-x) :=
    continuous_splineCorr.comp continuous_neg
  obtain ⟨_, hneg, hpos⟩ := negIndex_le_two_of_coprimeCrossDiff_eq_zero hΦ hpq hrs hall
  change negIndex ratCorr ≤ 2 at hneg
  change RenormalizedIntersectionTheory.posIndex ratCorr ≤ 2 at hpos
  rcases negIndex_or_posIndex_ratCorr_eq_top with ht | ht
  · rw [ht] at hneg; exact ENat.coe_ne_top 2 (top_le_iff.mp hneg)
  · rw [ht] at hpos; exact ENat.coe_ne_top 2 (top_le_iff.mp hpos)

/-- **Unconditional pointwise approximation no-go for arbitrary separable prime-tower assemblies.**
No nontrivial net of separable prime-tower assemblies `towerAssembly (S i) (k i)` converges
pointwise on `ℚ_{>0}` to `ratCorr`. -/
theorem not_tendsto_towerAssembly_ratCorr {ι : Type*} {l : Filter ι} [l.NeBot]
    (S : ι → Finset Nat.Primes) (k : (i : ι) → S i → Multiplicative ℤ → ℂ) :
    ¬ ∀ u : posUnits, Tendsto (fun i => towerAssembly (S i) (k i) u) l (𝓝 (ratCorr u)) := by
  intro htend
  obtain ⟨u, hu, v, hv, hne⟩ := exists_coprimeCrossDiff_ratCorr_ne_zero
  have hlim : Tendsto (fun i => coprimeCrossDiff (towerAssembly (S i) (k i)) u v)
      l (𝓝 (coprimeCrossDiff ratCorr u v)) :=
    (((htend (u * v)).sub (htend u)).sub (htend v)).add (htend 1)
  have hzero : ∀ i, coprimeCrossDiff (towerAssembly (S i) (k i)) u v = 0 := fun i =>
    coprimeCrossDiff_towerAssembly_twoPrimeUnits
      (prime_ne (by norm_num [prime2, prime5]))
      (prime_ne (by norm_num [prime2, prime7]))
      (prime_ne (by norm_num [prime3, prime5]))
      (prime_ne (by norm_num [prime3, prime7]))
      (S i) (k i) hu hv
  simp_rw [hzero] at hlim
  exact hne (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-! ### Untruncated axial replication blow-up on the non-RH finite stratum -/

theorem polarIndex_sub_const (k : Multiplicative ℤ → ℂ) (z : ℂ) :
    polarIndex (fun m => k m - z) = polarIndex k := by
  have hsd : secondDiff (fun m => k m - z) = secondDiff k := by
    funext m
    have heq : (fun x => k x - z) = fun x => k x + (-z) := funext fun _ => sub_eq_add_neg _ _
    rw [heq, secondDiff_add, secondDiff_const, add_zero]
  rw [polarIndex_eq_negIndex_secondDiff, polarIndex_eq_negIndex_secondDiff, hsd]

theorem ratCorr_one_conj : conj (ratCorr 1) = ratCorr 1 := by
  simpa using (isHermKernel_ratCorr 1).symm

theorem ratCorr_prime_axis_eq_zetaKernel (p : Nat.Primes) :
    (fun m : Multiplicative ℤ => ratCorr (primeUnit p ^ Multiplicative.toAdd m)) =
      zetaKernel ∘ zpowersHom HeckeLattice (primeElt p.2) := by
  funext m
  rw [ratCorr_eq_zetaKernel, map_zpow, posUnitsToHecke_primeUnit]
  rfl

/-- **Untruncated axial replication lower bound.** When `0 < κ(K_ζ) < ⊤`, every non-blind prime
`p ∈ S` (`(p : ℕ) ∉ zetaBlindPrimes`) contributes at least `κ(K_ζ) - 1 ≥ 1` to the glued negative
index of `axialAssembly S ratCorr`. -/
theorem negIndex_archGlue_axialAssembly_ratCorr_ge {S : Finset Nat.Primes} (hS : S.Nonempty)
    {c : ℝ} (hc : 0 < c) (hpos : 0 < negIndex zetaKernel) (hfin : negIndex zetaKernel < ⊤) :
    ((S.filter fun p : Nat.Primes => (p : ℕ) ∉ zetaBlindPrimes).card : ℕ∞) + 1 ≤
      negIndex (archGlue (axialAssembly S ratCorr) c) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hS
  have hR : (rightZeros zetaZeroConfig).Finite := by
    rw [← Set.encard_lt_top_iff, ← negIndex_zetaKernel]; exact hfin
  obtain ⟨m, hm_eq⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hle1 : negIndex zetaKernel ≤ 1 := by
      rw [← hm_eq]; exact Nat.cast_le.mpr (by omega)
    exact hpos.ne' (negIndex_zetaKernel_le_one_iff.mp hle1)
  set k : S → Multiplicative ℤ → ℂ := fun p n =>
    ratCorr (primeUnit (p : Nat.Primes) ^ Multiplicative.toAdd n) -
      if (p : Nat.Primes) = p₀ then 0 else ratCorr 1
  have hk_herm : ∀ p : S, IsHermKernel (k p) := fun p n => by
    show k p n⁻¹ = conj (k p n)
    have haxis : IsHermKernel (zetaKernel ∘ zpowersHom HeckeLattice (primeElt (p : Nat.Primes).2)) :=
      isHermKernel_zetaKernel.comp _
    have h1 := haxis n
    rw [← ratCorr_prime_axis_eq_zetaKernel (p : Nat.Primes)] at h1
    dsimp only at h1
    simp only [k, map_sub]
    rw [h1]
    split_ifs <;> simp [ratCorr_one_conj]
  have hpol_ge : ∀ p : S, ((p : Nat.Primes) : ℕ) ∉ zetaBlindPrimes → 1 ≤ polarIndex (k p) := by
    intro p hnb
    have hpol_eq : polarIndex (k p) = polarIndex
        (zetaKernel ∘ zpowersHom HeckeLattice (primeElt (p : Nat.Primes).2)) := by
      rw [show k p = fun n => ratCorr (primeUnit (p : Nat.Primes) ^ Multiplicative.toAdd n) -
        (if (p : Nat.Primes) = p₀ then 0 else ratCorr 1) from rfl,
        polarIndex_sub_const, ratCorr_prime_axis_eq_zetaKernel]
    rw [hpol_eq]
    have hle := negIndex_le_polarIndex_add_one
      (zetaKernel ∘ zpowersHom HeckeLattice (primeElt (p : Nat.Primes).2))
    rw [negIndex_zetaKernel_prime_eq hR (p : Nat.Primes).2 hnb, ← hm_eq] at hle
    have h2le : (1 : ℕ∞) + 1 ≤ polarIndex
        (zetaKernel ∘ zpowersHom HeckeLattice (primeElt (p : Nat.Primes).2)) + 1 :=
      (Nat.cast_le.mpr hm2).trans hle
    exact WithTop.le_of_add_le_add_right (ENat.coe_ne_top 1) h2le
  rw [axialAssembly_eq_towerAssembly_of_nonempty hp₀ ratCorr]
  have hlo := towerSignature_lower S hk_herm hc
  refine le_trans ?_ hlo
  gcongr
  have hcard : ((S.filter fun p : Nat.Primes => (p : ℕ) ∉ zetaBlindPrimes).card : ℕ∞) =
      ∑ p : S, if ((p : Nat.Primes) : ℕ) ∉ zetaBlindPrimes then (1 : ℕ∞) else 0 := by
    rw [Finset.sum_boole]
    congr 1
    symm
    apply Finset.card_bij (fun (p : S) _ => (p : Nat.Primes))
    · intro p hp
      exact mem_filter.mpr ⟨p.2, (mem_filter.mp hp).2⟩
    · intro p₁ _ p₂ _ h
      exact Subtype.ext h
    · intro q hq
      obtain ⟨hqS, hnb⟩ := mem_filter.mp hq
      exact ⟨⟨q, hqS⟩, mem_filter.mpr ⟨mem_univ _, hnb⟩, rfl⟩
  rw [hcard]
  refine sum_le_sum fun p _ => ?_
  by_cases hnb : ((p : Nat.Primes) : ℕ) ∉ zetaBlindPrimes
  · rw [if_pos hnb]; exact hpol_ge p hnb
  · rw [if_neg hnb]; exact zero_le

/-- **Untruncated axial replication divergence.** On the non-RH finite stratum
`0 < κ(K_ζ) < ⊤`, the glued negative index of `axialAssembly S ratCorr` diverges to `⊤` along the
directed family `atTop` of finite prime sets `S`. -/
theorem tendsto_negIndex_archGlue_axialAssembly_ratCorr_atTop {c : ℝ} (hc : 0 < c)
    (hpos : 0 < negIndex zetaKernel) (hfin : negIndex zetaKernel < ⊤) :
    Tendsto (fun S : Finset Nat.Primes => negIndex (archGlue (axialAssembly S ratCorr) c))
      atTop (𝓝 ⊤) := by
  classical
  have hR : (rightZeros zetaZeroConfig).Finite := by
    rw [← Set.encard_lt_top_iff, ← negIndex_zetaKernel]; exact hfin
  have hblind_fin : ({p : Nat.Primes | (p : ℕ) ∈ zetaBlindPrimes}).Finite :=
    (zetaBlindPrimes_finite_card_le hR).1.preimage Subtype.val_injective.injOn
  have hinf_nonblind : ({p : Nat.Primes | (p : ℕ) ∉ zetaBlindPrimes}).Infinite := by
    haveI : Infinite Nat.Primes := Nat.infinite_setOf_prime.to_subtype
    have huniv : (Set.univ : Set Nat.Primes).Infinite := Set.infinite_univ
    exact (huniv.sdiff hblind_fin).mono fun p hp => hp.2
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro m
  obtain ⟨T, hT_sub, hT_card⟩ := hinf_nonblind.exists_subset_card_eq (max m 1)
  have hT_ne : T.Nonempty := Finset.card_pos.mp (by rw [hT_card]; positivity)
  filter_upwards [eventually_ge_atTop T] with S hTS
  have hS_ne : S.Nonempty := hT_ne.mono hTS
  have hsub : T ⊆ S.filter fun p : Nat.Primes => (p : ℕ) ∉ zetaBlindPrimes := fun p hp =>
    mem_filter.mpr ⟨hTS hp, hT_sub hp⟩
  have hm_lt : (m : ℕ∞) < ((m + 1 : ℕ) : ℕ∞) := Nat.cast_lt.mpr (Nat.lt_succ_self m)
  have hm_le : ((m + 1 : ℕ) : ℕ∞) ≤
      ((S.filter fun p : Nat.Primes => (p : ℕ) ∉ zetaBlindPrimes).card : ℕ∞) + 1 := by
    have hle : m + 1 ≤ (S.filter fun p : Nat.Primes => (p : ℕ) ∉ zetaBlindPrimes).card + 1 :=
      Nat.add_le_add_right ((le_max_left m 1).trans (hT_card.symm.le.trans (Finset.card_le_card hsub))) 1
    exact_mod_cast hle
  exact hm_lt.trans_le (hm_le.trans
    (negIndex_archGlue_axialAssembly_ratCorr_ge hS_ne hc hpos hfin))

end GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling
