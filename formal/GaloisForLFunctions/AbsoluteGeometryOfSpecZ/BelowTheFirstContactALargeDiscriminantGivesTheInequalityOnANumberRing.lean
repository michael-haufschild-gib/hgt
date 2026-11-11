import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction
import GaloisForLFunctions.RHTower.DirichletArchimedeanSymbolPositivity

/-!
# Below the first contact a large discriminant gives the inequality on a number ring

A packet shorter than `log 2` meets no contact of a number ring: a prime ideal has norm at least
`2`. On such packets Weil's form of a Hecke character is the pole plane, the conductor on the
mass, and the forms of the places, and the symbol of a place is bounded below: `Γ_ℝ(s)` by
`−log 128π`, `Γ_ℝ(s + 1)` by `−log 4π`.

* **The places on a packet** (`archForm_add_log_mul_mass_nonneg`,
  `archForm_add_conjugateForm_add_log_mul_mass_nonneg`): the archimedean form of `ℤ` is at least
  `−log(128π)` times the mass; with the conjugate form it is at least `−log(4π)` times the mass.
* **A Hecke character below its first contact** (`heckeZeroSum_ge_of_no_contact`,
  `heckeZeroSum_nonneg_of_no_contact`): with `d` the degree, `c` the number of factors
  `Γ_ℝ(s + 1)` and `N` the conductor scale,
  `Z_ψ(f) ≥ m_ψ 2d₁d₂ + (log N − (d − c) log 128π − c log 4π) ∫f²`. For a nontrivial character
  with `N ≥ (128π)^{d−c}(4π)^c` the form is nonnegative there.
* **The square of a number ring** (`dedekindZeroSum_ge_zeroSum_of_no_contact`,
  `tendsto_ringForm_le_degrees_of_short`): if
  `|d_K| ≥ (128π)^{r₁ + r₂ − 1}(4π)^{r₂}`, then on packets shorter than `log 2` the zero sum of
  the Dedekind zeta function is at least that of `ζ`, and the pairing of the ideals has a limit,
  at most `2 d₁ d₂ − ∫f²/5000`: the inequality of Castelnuovo and Severi holds on the square of
  the ring where no contact enters.

The discriminant is the density of the comb of the ring; the inequality below the first contact
is the statement that this density exceeds the constants of the places. Nothing is used of the
field but its signature and its discriminant.
-/

noncomputable section

open Finset Filter Topology MeasureTheory NumberField
open Zeta23
open scoped Classical Real

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions ArtinMertens

local notation "cx(" f ")" => fun u : ℝ => ((f u : ℝ) : ℂ)

variable {f : ℝ → ℝ}

/-! ### A short packet meets no contact -/

/-- A packet of width `2a` has no autocorrelation beyond `2a`. -/
theorem packetAutocorr_eq_zero_of_short {c a : ℝ} (hshort : ∀ u, a < |u - c| → f u = 0)
    {x : ℝ} (hx : 2 * a < |x|) : packetAutocorr f x = 0 := by
  rw [packetAutocorr]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  show f u * f (u + x) = 0
  by_contra h
  have h1 : f u ≠ 0 := left_ne_zero_of_mul h
  have h2 : f (u + x) ≠ 0 := right_ne_zero_of_mul h
  have h1' : |u - c| ≤ a := not_lt.mp fun hlt => h1 (hshort u hlt)
  have h2' : |u + x - c| ≤ a := not_lt.mp fun hlt => h2 (hshort _ hlt)
  have hx' : |x| ≤ 2 * a := by
    calc |x| = |(u + x - c) - (u - c)| := by
          congr 1
          ring
      _ ≤ |u + x - c| + |u - c| := abs_sub _ _
      _ ≤ 2 * a := by linarith
  linarith

/-- A packet shorter than `log 2` meets no contact. -/
theorem packetAutocorr_log_eq_zero_of_short {c a : ℝ} (ha : 2 * a < Real.log 2)
    (hshort : ∀ u, a < |u - c| → f u = 0) (n : ℕ) (hn : 1 < n) :
    packetAutocorr f (Real.log n) = 0 := by
  refine packetAutocorr_eq_zero_of_short hshort ?_
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos h2
  have h0 : 0 ≤ Real.log (n : ℝ) := (Real.log_pos one_lt_two).le.trans hlog
  rw [abs_of_nonneg h0]
  linarith

theorem packetAutocorr_zero_nonneg (f : ℝ → ℝ) : 0 ≤ packetAutocorr f 0 := by
  rw [packetAutocorr]
  refine integral_nonneg fun u => ?_
  show 0 ≤ f u * f (u + 0)
  rw [add_zero]
  exact mul_self_nonneg _

/-! ### The places on a packet -/

section Arch

variable (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)

include hf hfc

/-- Plancherel: the mass of a packet. -/
theorem mass_eq_integral_normSq :
    1 / (2 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 = packetAutocorr f 0 := by
  have hF : ContDiff ℝ 2 cx(f) := contDiff_ofReal_packet hf
  obtain ⟨a, -, hFs⟩ := exists_tsupport_ofReal_subset hfc
  have hm : ∫ u, f u ^ 2 = packetAutocorr f 0 := by
    rw [packetAutocorr]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show f u ^ 2 = f u * f (u + 0)
      rw [add_zero, sq])
  rw [_root_.RHTower.integral_norm_paperFT_sq hF hFs, integral_norm_ofReal_sq, hm]
  field_simp

/-- The archimedean form of `ℤ` on a packet is the energy of its symbol. -/
theorem archForm_eq_integral_normSq :
    1 / (2 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t =
      EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x := by
  have hF : ContDiff ℝ 2 cx(f) := contDiff_ofReal_packet hf
  have hFc : HasCompactSupport cx(f) := hasCompactSupport_ofReal_packet hfc
  obtain ⟨R, hsuppR⟩ := exists_natCast_le_abs_imp_eq_zero hfc
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfc (by norm_num)
  have hB' : ∀ u, |f u| ≤ B := fun u => by
    rw [← Real.norm_eq_abs]
    exact hB u
  have hLip : ∀ u v, |f u - f v| ≤ (C : ℝ) * |u - v| := fun u v => by
    have h := hC.dist_le_mul u v
    rwa [Real.dist_eq, Real.dist_eq] at h
  have hweil : _root_.RHTower.WeilOneSided.weilArchRe (EF.weilTest cx(f) cx(f)) -
        (_root_.RHTower.weilPoleTerm (EF.weilTest cx(f) cx(f))).re =
      EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x :=
    weilArchRe_sub_pole_packet hf hfc hsuppR hB' hLip
  rw [← hweil]
  exact (_root_.RHTower.BlindPrimePowerSlack.weilArchRe_sub_pole_eq ⟨cx(f), hF, hFc⟩).symm

/-- **The form of `Γ_ℝ(s)` on a packet is at least `−log(128π)` times the mass.** -/
theorem archForm_add_log_mul_mass_nonneg :
    0 ≤ EF.gammaBracket 0 * packetAutocorr f 0 + (∫ x in Set.Ioi 0, levyJump f x) +
      Real.log (128 * π) * packetAutocorr f 0 := by
  have hF : ContDiff ℝ 2 cx(f) := contDiff_ofReal_packet hf
  have hFc : HasCompactSupport cx(f) := hasCompactSupport_ofReal_packet hfc
  have hi0 : Integrable fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 :=
    _root_.RHTower.BlindPrimePowerSlack.integrable_normSq_paperFT ⟨cx(f), hF, hFc⟩
  have hi1 : Integrable fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t :=
    _root_.RHTower.BlindPrimePowerSlack.integrable_normSq_paperFT_mul_gammaBracket
      ⟨cx(f), hF, hFc⟩
  have j0 : Integrable fun t : ℝ => Real.log (128 * π) * ‖paperFT cx(f) t‖ ^ 2 :=
    hi0.const_mul _
  have hnn : 0 ≤ 1 / (2 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 *
      (EF.gammaBracket t + Real.log (128 * π)) :=
    mul_nonneg (by positivity) (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (by
      rw [_root_.RHTower.WeilPoleWeight.gammaBracket_eq_archimedeanWeilSymbol]
      exact _root_.RHTower.evenDirichletArchSymbol_nonneg le_rfl t))
  have e : (fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 * (EF.gammaBracket t + Real.log (128 * π))) =
      fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t +
        Real.log (128 * π) * ‖paperFT cx(f) t‖ ^ 2 := funext fun t => by ring
  rw [e, integral_add hi1 j0, integral_const_mul, mul_add, ← mul_assoc,
    mul_comm (1 / (2 * π)) (Real.log (128 * π)), mul_assoc, mass_eq_integral_normSq hf hfc,
    archForm_eq_integral_normSq hf hfc] at hnn
  exact hnn

/-- **The form of `Γ_ℝ(s + 1)` on a packet is at least `−log(4π)` times the mass.** -/
theorem archForm_add_conjugateForm_add_log_mul_mass_nonneg :
    0 ≤ EF.gammaBracket 0 * packetAutocorr f 0 + (∫ x in Set.Ioi 0, levyJump f x) +
      conjugateForm f + Real.log (4 * π) * packetAutocorr f 0 := by
  have hF : ContDiff ℝ 2 cx(f) := contDiff_ofReal_packet hf
  have hFc : HasCompactSupport cx(f) := hasCompactSupport_ofReal_packet hfc
  have hi0 : Integrable fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 :=
    _root_.RHTower.BlindPrimePowerSlack.integrable_normSq_paperFT ⟨cx(f), hF, hFc⟩
  have hi1 : Integrable fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t :=
    _root_.RHTower.BlindPrimePowerSlack.integrable_normSq_paperFT_mul_gammaBracket
      ⟨cx(f), hF, hFc⟩
  have hi2 : Integrable fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 * (π / Real.cosh (π * t)) := by
    refine hi0.mul_bdd (c := π) ?_ (Eventually.of_forall fun t => ?_)
    · exact (continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
        fun t => (Real.cosh_pos _).ne').aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (div_pos Real.pi_pos (Real.cosh_pos _))]
      exact div_le_self Real.pi_pos.le (Real.one_le_cosh _)
  have j0 : Integrable fun t : ℝ => Real.log (4 * π) * ‖paperFT cx(f) t‖ ^ 2 := hi0.const_mul _
  have j12 : Integrable fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t +
      ‖paperFT cx(f) t‖ ^ 2 * (π / Real.cosh (π * t)) := hi1.add hi2
  have hnn : 0 ≤ 1 / (2 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 *
      (EF.gammaBracket t + Real.log (4 * π) + π / Real.cosh (π * t)) :=
    mul_nonneg (by positivity) (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (by
      rw [_root_.RHTower.WeilPoleWeight.gammaBracket_eq_archimedeanWeilSymbol]
      exact _root_.RHTower.oddDirichletArchSymbol_nonneg le_rfl t))
  have e : (fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 *
        (EF.gammaBracket t + Real.log (4 * π) + π / Real.cosh (π * t))) =
      fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t +
          ‖paperFT cx(f) t‖ ^ 2 * (π / Real.cosh (π * t)) +
        Real.log (4 * π) * ‖paperFT cx(f) t‖ ^ 2 := funext fun t => by ring
  have hS : 1 / (2 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 * (π / Real.cosh (π * t)) =
      conjugateForm f := placeEnergy_eq_conjugateForm hf hfc
  have hP := mass_eq_integral_normSq hf hfc
  have hG := archForm_eq_integral_normSq hf hfc
  rw [e, integral_add j12 j0, integral_add hi1 hi2, integral_const_mul] at hnn
  have hlin : 1 / (2 * π) * ((∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t) +
        (∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 * (π / Real.cosh (π * t))) +
        Real.log (4 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2) =
      1 / (2 * π) * (∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t) +
        1 / (2 * π) * (∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 * (π / Real.cosh (π * t))) +
        Real.log (4 * π) * (1 / (2 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2) := by ring
  rw [hlin, hG, hS, hP] at hnn
  exact hnn

end Arch

/-! ### A Hecke character below its first contact -/

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

theorem heckeConjugatePlaces_le (ψ : HeckeCharacter 𝔪) :
    heckeConjugatePlaces 𝔪 ψ ≤ placeDegree K := by
  rw [heckeConjugatePlaces, placeDegree]
  have h : ∑ v : {v : InfinitePlace K // v.IsReal},
      (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat ≤
        Fintype.card {v : InfinitePlace K // v.IsReal} := by
    calc ∑ v : {v : InfinitePlace K // v.IsReal}, (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat
        ≤ ∑ _v : {v : InfinitePlace K // v.IsReal}, 1 :=
          Finset.sum_le_sum fun v _ => Bool.toNat_le _
      _ = Fintype.card {v : InfinitePlace K // v.IsReal} := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega

/-- The conductor and the places of a Hecke character on a packet: at least the mass times
`log N − (d − c) log 128π − c log 4π`. -/
theorem heckeArchPacket_ge (ψ : HeckeCharacter 𝔪) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (Real.log (heckeCompletionNorm 𝔪 : ℝ) -
        ((placeDegree K : ℝ) - heckeConjugatePlaces 𝔪 ψ) * Real.log (128 * π) -
        (heckeConjugatePlaces 𝔪 ψ : ℝ) * Real.log (4 * π)) * packetAutocorr f 0 ≤
      Real.log (heckeCompletionNorm 𝔪 : ℝ) * packetAutocorr f 0 +
        (placeDegree K : ℝ) *
          (EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x) +
        (heckeConjugatePlaces 𝔪 ψ : ℝ) * conjugateForm f := by
  have h1 := archForm_add_log_mul_mass_nonneg hf hfc
  have h2 := archForm_add_conjugateForm_add_log_mul_mass_nonneg hf hfc
  have hcd : (heckeConjugatePlaces 𝔪 ψ : ℝ) ≤ placeDegree K := by
    exact_mod_cast heckeConjugatePlaces_le 𝔪 ψ
  have p1 := mul_nonneg (sub_nonneg.mpr hcd) h1
  have p2 := mul_nonneg (Nat.cast_nonneg (heckeConjugatePlaces 𝔪 ψ) : (0 : ℝ) ≤ _) h2
  linarith

/-- **A Hecke character below its first contact.** -/
theorem heckeZeroSum_ge_of_no_contact (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hQ : ∀ n : ℕ, 1 < n → packetAutocorr f (Real.log n) = 0) :
    (heckePole 𝔪 ψ).re *
        (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) +
      (Real.log (heckeCompletionNorm 𝔪 : ℝ) -
        ((placeDegree K : ℝ) - heckeConjugatePlaces 𝔪 ψ) * Real.log (128 * π) -
        (heckeConjugatePlaces 𝔪 ψ : ℝ) * Real.log (4 * π)) * packetAutocorr f 0 ≤
      heckeZeroSum 𝔪 ψ hψ f := by
  have hempty : Icc 2 1 = (∅ : Finset ℕ) := Finset.Icc_eq_empty_of_lt (by norm_num)
  rw [heckeZeroSum_eq_heckePacketForm 𝔪 ψ hψ hf hfc hQ, heckePacketForm, hempty,
    Finset.sum_empty, mul_zero, sub_zero]
  have := heckeArchPacket_ge 𝔪 ψ hf hfc
  linarith

/-- **A nontrivial character of large conductor is positive below its first contact.** -/
theorem heckeZeroSum_nonneg_of_no_contact {ψ : HeckeCharacter 𝔪} (hψ1 : ψ ≠ 1)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    (hN : ((placeDegree K : ℝ) - heckeConjugatePlaces 𝔪 ψ) * Real.log (128 * π) +
      (heckeConjugatePlaces 𝔪 ψ : ℝ) * Real.log (4 * π) ≤
        Real.log (heckeCompletionNorm 𝔪 : ℝ))
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hQ : ∀ n : ℕ, 1 < n → packetAutocorr f (Real.log n) = 0) :
    0 ≤ heckeZeroSum 𝔪 ψ hψ f := by
  have h := heckeZeroSum_ge_of_no_contact 𝔪 ψ hψ hf hfc hQ
  have hpole : (heckePole 𝔪 ψ).re = 0 := by
    rw [heckePole, if_neg hψ1, Complex.zero_re]
  rw [hpole, zero_mul, zero_add] at h
  exact le_trans (mul_nonneg (by linarith) (packetAutocorr_zero_nonneg f)) h

/-! ### The square of a number ring below its first contact -/

variable (K)

/-- A number field has a place: `r₂ + 1 ≤ r₁ + 2 r₂`. -/
theorem nrComplexPlaces_add_one_le_placeDegree :
    InfinitePlace.nrComplexPlaces K + 1 ≤ placeDegree K := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  unfold InfinitePlace.nrRealPlaces at h
  rw [← Nat.card_eq_fintype_card] at h
  rw [placeDegree, ← Nat.card_eq_fintype_card]
  omega

/-- **Below the first contact the zero sum of the ring dominates that of `ℤ`**, once the
discriminant exceeds the constants of the places other than the first. -/
theorem dedekindZeroSum_ge_zeroSum_of_no_contact
    (hdisc : ((placeDegree K : ℝ) - 1 - InfinitePlace.nrComplexPlaces K) * Real.log (128 * π) +
      (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log (4 * π) ≤
        Real.log |(NumberField.discr K : ℝ)|)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hQ : ∀ n : ℕ, 1 < n → packetAutocorr f (Real.log n) = 0) :
    zeroSum f ≤ dedekindZeroSum K f := by
  have hempty : Icc 2 1 = (∅ : Finset ℕ) := Finset.Icc_eq_empty_of_lt (by norm_num)
  have h1 := archForm_add_log_mul_mass_nonneg hf hfc
  have h2 := archForm_add_conjugateForm_add_log_mul_mass_nonneg hf hfc
  have hmass := packetAutocorr_zero_nonneg f
  have hr : (InfinitePlace.nrComplexPlaces K : ℝ) + 1 ≤ placeDegree K := by
    exact_mod_cast nrComplexPlaces_add_one_le_placeDegree K
  have p1 := mul_nonneg (by linarith : (0 : ℝ) ≤
    (placeDegree K : ℝ) - 1 - InfinitePlace.nrComplexPlaces K) h1
  have p2 := mul_nonneg (Nat.cast_nonneg (InfinitePlace.nrComplexPlaces K) : (0 : ℝ) ≤ _) h2
  have p3 := mul_nonneg (sub_nonneg.mpr hdisc) hmass
  rw [dedekindZeroSum, heckeZeroSum_eq_heckePacketForm (trivialModulus K) 1
      (heckeFiniteConductor_trivialModulus K 1) hf hfc hQ, heckePacketForm,
    zeroSum_eq_packetForm hf hfc hQ, packetForm, heckePole_trivialModulus_one,
    heckeConjugatePlaces_trivialModulus, heckeCompletionNorm_trivialModulus, Complex.one_re,
    one_mul, hempty, Finset.sum_empty, Finset.sum_empty, mul_zero, sub_zero, sub_zero]
  linarith

/-- **The inequality of Castelnuovo and Severi on the square of a number ring, where no contact
enters.** If `|d_K| ≥ (128π)^{r₁+r₂−1}(4π)^{r₂}`, then for a packet shorter than `log 2` the
pairing of the ideals has a limit, at most `2 d₁ d₂ − ∫f²/5000`. -/
theorem tendsto_ringForm_le_degrees_of_short
    (hdisc : ((placeDegree K : ℝ) - 1 - InfinitePlace.nrComplexPlaces K) * Real.log (128 * π) +
      (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log (4 * π) ≤
        Real.log |(NumberField.discr K : ℝ)|)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K₀ : ℕ} (hK : 1 ≤ K₀)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K₀ ≤ u → f u = 0) {c a : ℝ}
    (ha : 2 * a < Real.log 2) (hshort : ∀ u, a < |u - c| → f u = 0) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => ringForm K f (3 * K₀) N +
          2 * weightedContact (idealContact K) f (3 * K₀) N) atTop (𝓝 l) ∧
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        1 / 5000 * ∫ u, f u ^ 2 := by
  refine ⟨_, tendsto_ringForm_add_idealContact K hf hfc hK hsupp, ?_⟩
  have h1 := zeroSum_ge_of_width hf hfc (c := c) fun u hu => hshort u (by
    have := Real.log_two_lt_d9
    linarith)
  have h2 := dedekindZeroSum_ge_zeroSum_of_no_contact K hdisc hf hfc
    (packetAutocorr_log_eq_zero_of_short ha hshort)
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
