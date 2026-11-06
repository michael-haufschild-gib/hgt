import GaloisForLFunctions.ArithmeticKreinLangerTheory.AttainedDepthIsSeenByAlmostEveryPrime
import GaloisForLFunctions.ArithmeticCouplingTheory.TheConeCouplingHasNoDeepestZero
import GaloisForLFunctions.HeckeKreinToeplitz.IndexIsEnergy
import GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.JointAncestryConstantVectorDyadicShellDetection

/-!
# Prime towers, positive-cone coupling, and the asymptotic abscissa law

`AttainedDepthIsSeenByAlmostEveryPrime` showed that an attained minimal real part below `½` fails
positivity on almost every prime tower, making RH equivalent to positivity on infinitely many prime
towers *conditional* on attainedness (`riemannHypothesis_iff_infinite_primes_posDef_of_attained`).
Meanwhile `TheConeCouplingHasNoDeepestZero` proved that bounded coupling on the positive cone
`⟨p⟩₊ × ⟨q⟩₊` excludes a deepest off-line zero without forcing zeros to approach the line
(`PositiveQuartetsWithBoundedConeCoupling`).

This module removes the conditional attainedness premise, sharpens prime-tower positivity to mere
forward-power boundedness, and establishes three unconditional arithmetic producers of
`RHTower.AsymptoticAbscissaLaw` together with the full collapse of finite-stratum and large-height
criteria under `AsymptoticAbscissaLaw`:

* **Bounded prime towers see attained depth** (`finite_primes_bounded_of_attained_depth`,
  `zeta_finite_primes_bounded_of_attained_depth`): `tsum_weight_node_eq_zero_of_bounded` needs only
  forward-power boundedness `∃ B, ∀ n : ℕ, ‖K(p^n)‖ ≤ B`, not positive definiteness. An attained
  minimal real part `< ½` therefore leaves `K_ζ` bounded on only finitely many prime towers.
* **Unconditional prime-tower producers and RH splits**
  (`asymptoticAbscissaLaw_of_infinite_primes_bounded`,
  `asymptoticAbscissaLaw_of_infinite_primes_posDef`,
  `riemannHypothesis_iff_zerosApproachLine_and_infinite_primes_bounded`,
  `riemannHypothesis_iff_zerosApproachLine_and_infinite_primes_posDef`): boundedness (hence also
  positive definiteness) of `K_ζ` on infinitely many prime towers unconditionally implies
  `AsymptoticAbscissaLaw`, replacing the attainedness hypothesis `hatt` by `ZerosApproachLine`.
* **Positive-cone two-prime coupling and dyadic-shell producers**
  (`asymptoticAbscissaLaw_of_bounded_coneCoupling`,
  `riemannHypothesis_iff_zerosApproachLine_and_bounded_coneCoupling`,
  `asymptoticAbscissaLaw_of_frequently_jasConstProductPositiveOn_shell`): bounded coupling on
  `⟨p⟩₊ × ⟨q⟩₊` for any distinct primes `p ≠ q`, and level-one constant-vector joint-ancestry
  positivity on infinitely many dyadic prime shells `(N, 2N]`, each unconditionally produce
  `AsymptoticAbscissaLaw`.
* **Collapse atlas under `AsymptoticAbscissaLaw`**
  (`finite_re_gt_iff_forall_re_le_of_asymptoticAbscissaLaw`,
  `riemannHypothesis_tfae_of_asymptoticAbscissaLaw`): under `AsymptoticAbscissaLaw` alone, RH is
  equivalent to `ZerosApproachLine`, `FiniteOffLine`, `κ(K_ζ) < ∞`, bounded de Bruijn–Newman
  nonreal zero counts, finite critical source energy `E_crit ≠ ⊤`, `EventualHadamardPositivity`,
  and `EventualFilteredCentralGapBudget`.
-/

open Complex Finset Filter Topology Set
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests cx_contDiff cx_hasCompactSupport
  summable_norm_Wsummand)
open GaloisForLFunctions.ArithmeticCouplingTheory (coupling ConeCoupling.riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling)
open GaloisForLFunctions.ArithmeticIndexDescent (xiCriticalSourceEnergy quadraticExclusionQuantum
  riemannHypothesis_iff_criticalEnergy_le_quantum)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)
open _root_.RHTower _root_.RHTower.BacklundConverse _root_.RHTower.LindelofSparse _root_.RHTower.DeBruijn
open _root_.RHTower.CrossRouteReceiverBridges (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip
  xiZeroCopy_mem_zetaZeroConfig_carrier)

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-! ### Forward-power boundedness and attained depth -/

/-- For a Hermitian kernel, boundedness on natural powers `u^n` (`n : ℕ`) is equivalent to
boundedness on the full cyclic group `u^m` (`m : ℤ`). -/
theorem IsHermKernel.exists_bound_pow_iff_zpow {G : Type*} [Group G] {k : G → ℂ}
    (hk : IsHermKernel k) (u : G) :
    (∃ B : ℝ, ∀ n : ℕ, ‖k (u ^ n)‖ ≤ B) ↔ ∃ B : ℝ, ∀ m : ℤ, ‖k (u ^ m)‖ ≤ B := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun m => ?_⟩
    cases m with
    | ofNat n => simpa using hB n
    | negSucc n =>
        rw [zpow_negSucc, hk, Complex.norm_conj]
        exact hB (n + 1)
  · rintro ⟨B, hB⟩
    exact ⟨B, fun n => by simpa using hB (n : ℕ)⟩

/-- **Almost every prime tower is unbounded on an attained positive depth.** If a zero `ρ₀` of
maximal depth `D > 0` has nonzero weight, the orbit kernel is bounded along `p^n` (`n : ℕ`) on
only finitely many prime towers. -/
theorem finite_primes_bounded_of_attained_depth {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {f : ℝ → ℝ} (hf : f ∈ realTests) {D : ℝ} (hD : 0 < D)
    (hmax : ∀ ρ ∈ Z.carrier, 1 / 2 - ρ.re ≤ D) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hdep : 1 / 2 - ρ₀.re = D) (hW₀ : Z.Wsummand (cx f) (cx f) ρ₀ ≠ 0) :
    {p : Nat.Primes | ∃ B : ℝ, ∀ n : ℕ, ‖orbitKernel Z f (primeElt p.2 ^ n)‖ ≤ B}.Finite := by
  classical
  set W : ℂ → ℂ := fun ρ => Z.Wsummand (cx f) (cx f) ρ with hWdef
  set A : Nat.Primes → Set Z.carrier := fun p =>
    {ρ | (ρ : ℂ) ≠ ρ₀ ∧ zeroChar ρ (primeElt p.2) = zeroChar ρ₀ (primeElt p.2)}
  have hdisj : ∀ p q, p ≠ q → Disjoint (A p) (A q) := fun p q hpq =>
    Set.disjoint_left.mpr fun ρ hp hq =>
      hpq (Subtype.ext (eq_of_alias_of_alias hp.1 p.2 q.2 hp.2 hq.2))
  have hsumW := summable_norm_Wsummand Z hZ (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
    (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
  refine (finite_of_disjoint_mass hdisj (b := fun ρ : Z.carrier => ‖W ρ‖) (fun _ => norm_nonneg _)
    hsumW (norm_pos_iff.mpr hW₀)).subset fun p hp => ?_
  have hlog : 0 < scale heckeLogScale (primeElt p.2) := by
    rw [scale_primeElt]; exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  set v := logChar heckeLogScale (1 / 2 - ρ₀) (primeElt p.2) with hvdef
  have hv : ‖v‖ = Real.exp (D * scale heckeLogScale (primeElt p.2)) := by
    rw [hvdef, norm_logChar, ← hdep]
    norm_num
  have hzero := tsum_weight_node_eq_zero_of_bounded hZ hf hD hmax hlog hp hv
  have hνinv : ∀ ρ : ℂ, logChar heckeLogScale (1 / 2 - ρ) (primeElt p.2) =
      (zeroChar ρ (primeElt p.2))⁻¹ := fun ρ => by
    show _ = (logChar heckeLogScale (ρ - 1 / 2) (primeElt p.2))⁻¹
    rw [← logChar_neg_apply, neg_sub]
  have hcond : ∀ ρ : ℂ, logChar heckeLogScale (1 / 2 - ρ) (primeElt p.2) = v ↔
      zeroChar ρ (primeElt p.2) = zeroChar ρ₀ (primeElt p.2) := fun ρ => by
    rw [hvdef, hνinv, hνinv, inv_inj]
  have hsplit : ∀ ρ : Z.carrier,
      (if logChar heckeLogScale (1 / 2 - (ρ : ℂ)) (primeElt p.2) = v then W ρ else 0) =
        (if ρ = ⟨ρ₀, hρ₀⟩ then W ρ₀ else 0) + (A p).indicator (fun ρ : Z.carrier => W ρ) ρ :=
    fun ρ => by
      by_cases h0 : ρ = ⟨ρ₀, hρ₀⟩
      · subst h0
        rw [if_pos rfl, if_pos rfl, Set.indicator_of_notMem (fun h => h.1 rfl), add_zero]
      · have h0' : (ρ : ℂ) ≠ ρ₀ := fun h => h0 (Subtype.ext h)
        rw [if_neg h0, zero_add]
        by_cases ha : zeroChar ρ (primeElt p.2) = zeroChar ρ₀ (primeElt p.2)
        · rw [if_pos ((hcond ρ).mpr ha), Set.indicator_of_mem (show ρ ∈ A p from ⟨h0', ha⟩)]
        · rw [if_neg fun h => ha ((hcond ρ).mp h),
            Set.indicator_of_notMem (show ρ ∉ A p from fun h => ha h.2)]
  have hsumI : Summable ((A p).indicator fun ρ : Z.carrier => W ρ) :=
    (hsumW.of_norm).indicator _
  have hsum0 : Summable fun ρ : Z.carrier => if ρ = ⟨ρ₀, hρ₀⟩ then W ρ₀ else 0 :=
    (hasSum_ite_eq _ _).summable
  rw [tsum_congr hsplit, hsum0.tsum_add hsumI, tsum_ite_eq] at hzero
  show ‖W ρ₀‖ ≤ ∑' ρ, (A p).indicator (fun ρ : Z.carrier => ‖W ρ‖) ρ
  rw [eq_neg_of_add_eq_zero_left hzero, norm_neg]
  refine (norm_tsum_le_tsum_norm hsumI.norm).trans (le_of_eq (tsum_congr fun ρ => ?_))
  exact norm_indicator_eq_indicator_norm (f := fun ρ : Z.carrier => W ρ) (a := ρ)

/-- **For `ζ`: an attained infimum of real parts below `½` leaves `K_ζ` bounded on only finitely
many prime towers.** -/
theorem zeta_finite_primes_bounded_of_attained_depth {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hre : ρ₀.re < 1 / 2)
    (hmin : ∀ ρ ∈ zetaZeroConfig.carrier, ρ₀.re ≤ ρ.re) :
    {p : Nat.Primes | ∃ B : ℝ, ∀ n : ℕ, ‖zetaKernel (primeElt p.2 ^ n)‖ ≤ B}.Finite :=
  finite_primes_bounded_of_attained_depth temperedConfig_zetaZeroConfig cubicSpline_mem_realTests
    (D := 1 / 2 - ρ₀.re) (by linarith) (fun ρ hρ => by have := hmin ρ hρ; linarith) hρ₀ rfl
    (zeta_Wsummand_ne_zero_of_left hρ₀ hre)

/-! ### Unconditional prime-tower producers of `AsymptoticAbscissaLaw` -/

/-- **Boundedness of `K_ζ` along infinitely many prime towers produces `AsymptoticAbscissaLaw`.** -/
theorem asymptoticAbscissaLaw_of_infinite_primes_bounded
    (hinf : {p : Nat.Primes | ∃ B : ℝ, ∀ n : ℕ, ‖zetaKernel (primeElt p.2 ^ n)‖ ≤ B}.Infinite) :
    AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_not_attainedTop ?_
  rintro ⟨β₀, hβ₀, ⟨q₁, hq₁⟩, hall⟩
  set σ : ℂ := (q₁.1 : ℂ)
  have hσ : σ ∈ zetaZeroConfig.carrier := xiZeroCopy_mem_zetaZeroConfig_carrier q₁
  set ρ₀ : ℂ := reflect σ
  have hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier := zetaZeroConfig.reflect_mem σ hσ
  have hρ₀re : ρ₀.re = 1 - β₀ := by rw [Zeta23.reflect_re, hq₁]
  have hre : ρ₀.re < 1 / 2 := by linarith
  have hmin : ∀ ρ ∈ zetaZeroConfig.carrier, ρ₀.re ≤ ρ.re := fun ρ hρ => by
    have hρ' : reflect ρ ∈ zetaZeroConfig.carrier := zetaZeroConfig.reflect_mem ρ hρ
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero
      (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ').1
    have hle : (reflect ρ).re ≤ β₀ := by rw [← hq]; exact hall q
    rw [Zeta23.reflect_re] at hle
    linarith
  exact hinf (zeta_finite_primes_bounded_of_attained_depth hρ₀ hre hmin)

/-- **Positive definiteness of `K_ζ` on infinitely many prime towers produces
`AsymptoticAbscissaLaw`.** -/
theorem asymptoticAbscissaLaw_of_infinite_primes_posDef
    (hinf : {p : Nat.Primes |
      IsPosDefKernel (zetaKernel ∘ zpowersHom _ (primeElt p.2))}.Infinite) :
    AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_infinite_primes_bounded (hinf.mono fun p hp => ?_)
  refine ⟨((zetaKernel ∘ zpowersHom _ (primeElt p.2)) 1).re, fun n => ?_⟩
  have := hp.norm_le (Multiplicative.ofAdd (n : ℤ))
  simpa [zpowersHom_apply] using this

/-- **Unconditional prime-tower boundedness split of RH.** Removing the attainedness hypothesis from
`riemannHypothesis_iff_infinite_primes_posDef_of_attained`: RH holds iff the zeros approach the
critical line and `K_ζ` is bounded along infinitely many prime towers. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_infinite_primes_bounded :
    RiemannHypothesis ↔ ZerosApproachLine ∧
      {p : Nat.Primes | ∃ B : ℝ, ∀ n : ℕ, ‖zetaKernel (primeElt p.2 ^ n)‖ ≤ B}.Infinite := by
  constructor
  · intro hRH
    have hpos : IsPosDefKernel zetaKernel := (isPosDefKernel_iff isHermKernel_zetaKernel).mpr
      (riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp hRH)
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, Set.infinite_univ.mono fun p _ => ?_⟩
    exact ⟨(zetaKernel 1).re, fun n => hpos.norm_le _⟩
  · rintro ⟨hZ, hinf⟩
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨hZ, asymptoticAbscissaLaw_of_infinite_primes_bounded hinf⟩

/-- **Unconditional prime-tower positivity split of RH.** RH holds iff the zeros approach the
critical line and `K_ζ` is positive definite on infinitely many prime towers. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_infinite_primes_posDef :
    RiemannHypothesis ↔ ZerosApproachLine ∧
      {p : Nat.Primes | IsPosDefKernel (zetaKernel ∘ zpowersHom _ (primeElt p.2))}.Infinite := by
  constructor
  · intro hRH
    have hpos : IsPosDefKernel zetaKernel := (isPosDefKernel_iff isHermKernel_zetaKernel).mpr
      (riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp hRH)
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH,
      Set.infinite_univ.mono fun p _ => hpos.comp _⟩
  · rintro ⟨hZ, hinf⟩
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨hZ, asymptoticAbscissaLaw_of_infinite_primes_posDef hinf⟩

/-! ### Positive-cone two-prime coupling and dyadic-shell producers -/

/-- A positive-definite kernel on a commutative group has coupling bounded by `4 Re K(1)`. -/
theorem norm_coupling_le_of_isPosDefKernel {G : Type*} [CommGroup G] {k : G → ℂ}
    (hk : IsPosDefKernel k) (u v : G) :
    ‖coupling k u v‖ ≤ 4 * (k 1).re := by
  unfold coupling
  calc ‖k (u * v) - k u - k v + k 1‖
      ≤ ‖k (u * v) - k u - k v‖ + ‖k 1‖ := norm_add_le _ _
    _ ≤ ‖k (u * v) - k u‖ + ‖k v‖ + ‖k 1‖ := by linarith [norm_sub_le (k (u * v) - k u) (k v)]
    _ ≤ ‖k (u * v)‖ + ‖k u‖ + ‖k v‖ + ‖k 1‖ := by linarith [norm_sub_le (k (u * v)) (k u)]
    _ ≤ 4 * (k 1).re := by linarith [hk.norm_le (u * v), hk.norm_le u, hk.norm_le v, hk.norm_le 1]

/-- **Bounded coupling on one positive two-prime cone `⟨p⟩₊ × ⟨q⟩₊` produces
`AsymptoticAbscissaLaw`.** -/
theorem asymptoticAbscissaLaw_of_bounded_coneCoupling {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q)
    (hbd : ∃ M : ℝ, ∀ a b : ℕ, ‖coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M) :
    AsymptoticAbscissaLaw := by
  rcases ConeCoupling.riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling hp hq hpq hbd with
    hRH | hno
  · exact asymptoticAbscissaLaw_of_riemannHypothesis hRH
  · refine asymptoticAbscissaLaw_of_not_attained fun q₀ => ?_
    obtain ⟨ρ, hρ, hlt⟩ := hno (q₀.1 : ℂ) (xiZeroCopy_mem_zetaZeroConfig_carrier q₀)
    obtain ⟨q', hq'⟩ := exists_xiZeroCopy_of_xi_eq_zero
      (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).1
    exact ⟨q', by rwa [hq']⟩

/-- **Sharp positive-cone coupling split of RH.** On `⟨p⟩₊ × ⟨q⟩₊` (`p ≠ q`), RH is equivalent to
`ZerosApproachLine` together with bounded coupling; `PositiveQuartetsWithBoundedConeCoupling` shows
that bounded cone coupling alone cannot force `ZerosApproachLine`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_bounded_coneCoupling {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) :
    RiemannHypothesis ↔ ZerosApproachLine ∧
      ∃ M : ℝ, ∀ a b : ℕ, ‖coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M := by
  constructor
  · intro hRH
    have hpos : IsPosDefKernel zetaKernel := (isPosDefKernel_iff isHermKernel_zetaKernel).mpr
      (riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp hRH)
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH,
      ⟨4 * (zetaKernel 1).re, fun a b => norm_coupling_le_of_isPosDefKernel hpos _ _⟩⟩
  · rintro ⟨hZ, hbd⟩
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨hZ, asymptoticAbscissaLaw_of_bounded_coneCoupling hp hq hpq hbd⟩

/-- **Level-one constant-vector joint-ancestry positivity on infinitely many dyadic prime shells
`(N, 2N]` produces `AsymptoticAbscissaLaw`.** -/
theorem asymptoticAbscissaLaw_of_frequently_jasConstProductPositiveOn_shell
    (hfr : ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow N (2 * N)) 1) :
    AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_not_attainedTopExcess ?_
  rintro ⟨Θ, hΘ, q₀, hq₀, hall⟩
  have hdist : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = |(xiSpectralPoint q).im| := fun q => by
    rw [spectral_im_eq, abs_sub_comm]
  have hoff : (q₀.1 : ℂ).re ≠ 1 / 2 := fun hre => by
    have := hdist q₀
    rw [hre, sub_self, abs_zero, hq₀] at this
    linarith
  have hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := fun q => by
    rw [hdist q, hdist q₀, hq₀]
    exact hall q
  exact not_frequently_jasConstProductPositiveOn_shell_of_maximal_offLine q₀ hoff hmax hfr

/-! ### Collapse of finite-stratum and large-height criteria under `AsymptoticAbscissaLaw` -/

/-- **Under `AsymptoticAbscissaLaw`, the asymptotic abscissa equals the abscissa at every `h ≥ 0`.** -/
theorem finite_re_gt_iff_forall_re_le_of_asymptoticAbscissaLaw (hAAL : AsymptoticAbscissaLaw)
    {h : ℝ} (hh : 0 ≤ h) :
    {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + h := by
  refine ⟨hAAL h hh, fun hall => Set.finite_empty.subset fun q hq => ?_⟩
  exact absurd (hall q) (not_le.mpr hq)

/-- **Under `AsymptoticAbscissaLaw`, eventual Hadamard positivity right of `½ + h` is global.** -/
theorem eventualHadamardPositivityRight_iff_forall_re_le_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) {h : ℝ} (hh : 0 ≤ h) :
    EventualHadamardPositivityRight (1 / 2 + h) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + h := by
  rw [eventualHadamardPositivityRight_iff hh]
  exact finite_re_gt_iff_forall_re_le_of_asymptoticAbscissaLaw hAAL hh

/-- **Under `AsymptoticAbscissaLaw`, the eventual Gaussian central-gap rate is the all-height rate.** -/
theorem eventualFilteredCentralGapRate_iff_filteredCentralGapRate_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) {h : ℝ} (hh : 0 ≤ h) :
    EventualFilteredCentralGapRate (h + h ^ 2 / 8) ↔ FilteredCentralGapRate (h + h ^ 2 / 8) := by
  rw [eventualFilteredCentralGapRate_iff_finite_re_gt hh, filteredCentralGapRate_iff_re_le hh]
  exact finite_re_gt_iff_forall_re_le_of_asymptoticAbscissaLaw hAAL hh

/-- **Under `AsymptoticAbscissaLaw`, RH is equivalent to `ZerosApproachLine`.** -/
theorem riemannHypothesis_iff_zerosApproachLine_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) :
    RiemannHypothesis ↔ ZerosApproachLine :=
  ⟨zerosApproachLine_of_riemannHypothesis, fun hZ =>
    riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr ⟨hZ, hAAL⟩⟩

/-- **Under `AsymptoticAbscissaLaw`, RH is equivalent to `FiniteOffLine`.** -/
theorem riemannHypothesis_iff_finiteOffLine_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) :
    RiemannHypothesis ↔ FiniteOffLine := by
  refine ⟨fun hRH => Set.finite_empty.subset fun q hq => ?_, fun hF =>
    (riemannHypothesis_iff_zerosApproachLine_of_asymptoticAbscissaLaw hAAL).mpr
      (zerosApproachLine_of_finiteOffLine hF)⟩
  apply (show (xiSpectralPoint q).im ≠ 0 from hq)
  rw [spectral_im_eq, xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q, sub_self]

/-- **Under `AsymptoticAbscissaLaw`, RH is equivalent to finite Krein–Langer index of `K_ζ`.** -/
theorem riemannHypothesis_iff_negIndex_zetaKernel_lt_top_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) :
    RiemannHypothesis ↔ negIndex zetaKernel < ⊤ := by
  rw [riemannHypothesis_iff_finiteOffLine_of_asymptoticAbscissaLaw hAAL]
  exact ((zetaKernel_finiteIndex_tfae Nat.prime_two Nat.prime_three (by norm_num)).out 2 0).symm

/-- **Under `AsymptoticAbscissaLaw`, RH is equivalent to bounded de Bruijn–Newman nonreal zero
counts.** -/
theorem riemannHypothesis_iff_bounded_nonrealZeroCount_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) :
    RiemannHypothesis ↔ ∃ M : ℕ, ∀ t, 0 < t → nonrealZeroCount t ≤ M := by
  rw [riemannHypothesis_iff_finiteOffLine_of_asymptoticAbscissaLaw hAAL]
  exact (zetaKernel_finiteIndex_tfae Nat.prime_two Nat.prime_three (by norm_num)).out 2 3

/-- **Under `AsymptoticAbscissaLaw`, RH is equivalent to finite critical source energy.** -/
theorem riemannHypothesis_iff_xiCriticalSourceEnergy_ne_top_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) :
    RiemannHypothesis ↔ xiCriticalSourceEnergy ≠ ⊤ := by
  constructor
  · intro hRH
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (riemannHypothesis_iff_criticalEnergy_le_quantum.mp hRH)
  · intro hE
    rw [riemannHypothesis_iff_negIndex_zetaKernel_lt_top_of_asymptoticAbscissaLaw hAAL]
    exact (negIndex_zetaKernel_le_of_energy hE).trans_lt (WithTop.coe_lt_top _)

/-- **Under `AsymptoticAbscissaLaw`, RH is equivalent to eventual Hadamard positivity.** -/
theorem riemannHypothesis_iff_eventualHadamardPositivity_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) :
    RiemannHypothesis ↔ EventualHadamardPositivity := by
  rw [eventualHadamardPositivity_iff_zerosApproachLine]
  exact riemannHypothesis_iff_zerosApproachLine_of_asymptoticAbscissaLaw hAAL

/-- **Under `AsymptoticAbscissaLaw`, RH is equivalent to a bounded large-height Gaussian
central-gap budget.** -/
theorem riemannHypothesis_iff_eventualFilteredCentralGapBudget_of_asymptoticAbscissaLaw
    (hAAL : AsymptoticAbscissaLaw) :
    RiemannHypothesis ↔ EventualFilteredCentralGapBudget := by
  rw [eventualFilteredCentralGapBudget_iff_finiteOffLine]
  exact riemannHypothesis_iff_finiteOffLine_of_asymptoticAbscissaLaw hAAL

/-- **Master collapse under `AsymptoticAbscissaLaw`.** -/
theorem riemannHypothesis_tfae_of_asymptoticAbscissaLaw (hAAL : AsymptoticAbscissaLaw) :
    [RiemannHypothesis,
      ZerosApproachLine,
      FiniteOffLine,
      negIndex zetaKernel < ⊤,
      ∃ M : ℕ, ∀ t, 0 < t → nonrealZeroCount t ≤ M,
      xiCriticalSourceEnergy ≠ ⊤,
      EventualHadamardPositivity,
      EventualFilteredCentralGapBudget].TFAE := by
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_zerosApproachLine_of_asymptoticAbscissaLaw hAAL
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_finiteOffLine_of_asymptoticAbscissaLaw hAAL
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_negIndex_zetaKernel_lt_top_of_asymptoticAbscissaLaw hAAL
  tfae_have 1 ↔ 5 := riemannHypothesis_iff_bounded_nonrealZeroCount_of_asymptoticAbscissaLaw hAAL
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_xiCriticalSourceEnergy_ne_top_of_asymptoticAbscissaLaw hAAL
  tfae_have 1 ↔ 7 := riemannHypothesis_iff_eventualHadamardPositivity_of_asymptoticAbscissaLaw hAAL
  tfae_have 1 ↔ 8 := riemannHypothesis_iff_eventualFilteredCentralGapBudget_of_asymptoticAbscissaLaw hAAL
  tfae_finish

end GaloisForLFunctions.ArithmeticKreinLangerTheory
