import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheZerosOfAHeckeLFunctionSatisfyWeilsExplicitFormula
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfAQuadraticRingPairsWithItsConductor
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormOnStepPacketsIsDeterminedByItsValuesOnWindows

/-!
# The ideals of a number ring pair as degree points with the zeros of its Hecke functions

Let `K` be a number field, abelian over `ℚ` or not, and `ψ` a primitive ray class character of
`K`. The ideals of the ring of integers, counted by their norms, sit on the comb of the
integers with the contacts `Re Λ_ψ(n)`, `Λ_ψ(n) = Σ_{N𝔭^k = n} ψ(𝔭)^k log N𝔭`.

* **The symbol of the places** (`heckeSymbol_eq`). On the critical line the archimedean term is
  `log N + d · (symbol of ℤ) + c · π/cosh(πt)`: `d = r₁ + 2r₂` the degree, `c` the number of
  factors `Γ_ℝ(s + 1)`: the real places where `ψ` is odd, and the complex places.
* **Weil's form on a packet through its autocorrelation**
  (`heckeZeroSum_eq_heckePacketForm`). For a real packet `f` with autocorrelation `h`,

  `Z_ψ(f) = m_ψ 2d₁d₂ + log N · h(0) + d (A(0) h(0) + ∫_{x>0} 2ω(x)(h(0) − h(x)) dx)
      + c ∫ h(x)/(2 cosh(x/2)) dx − 2 Σ_n Re Λ_ψ(n) n^{−1/2} h(log n)`.
* **The pairing of the ideals** (`tendsto_heckeForm_add_idealContact`). On the degree points of
  a window: `d` times the jets of the integers, minus `c` times the conjugate jets `1/(m + n)`,
  the counterterm with `log N`, and twice the contacts of the ideals tend to
  `m_ψ 2d₁d₂ − Z_ψ(f)`. For the trivial character this is the pairing of the square of the ring
  through its ideals: twice the product of the degrees minus the sum over the zeros of its
  Dedekind zeta function. A complex place carries the jets `1/|m − n|`.

The class group and the unit group do not enter the pairing of the ideals counted by norms: the
jets depend on the signature, the counterterm on discriminant and conductor, the contacts on the
values of `ψ` on the prime ideals.
-/

noncomputable section

open Finset Filter Topology MeasureTheory NumberField
open Zeta23 Zeta23.WeilEF
open scoped Classical ComplexConjugate Real

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions ArtinMertens

local notation "cx(" f ")" => fun u : ℝ => ((f u : ℝ) : ℂ)

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-! ### The symbol of the places -/

/-- The degree of the field counted by its places: one for a real, two for a complex place. -/
def placeDegree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Fintype.card {v : InfinitePlace K // v.IsReal} + 2 * InfinitePlace.nrComplexPlaces K

/-- The number of factors `Γ_ℝ(s + 1)` of `L(s, ψ)`: the real places where `ψ` is odd, and the
complex places. -/
def heckeConjugatePlaces (ψ : HeckeCharacter 𝔪) : ℕ :=
  (∑ v : {v : InfinitePlace K // v.IsReal}, (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat) +
    InfinitePlace.nrComplexPlaces K

theorem two_pi_mul_muq (κ : ℕ) (t : ℝ) :
    2 * π * Zeta23.ThmE.muq κ 1 t =
      Real.log (((1 : ℕ) : ℝ) / π) +
        (Complex.digamma (1 / 4 + (κ : ℂ) / 2 + Complex.I * t / 2)).re := by
  rw [Zeta23.ThmE.muq, ← mul_assoc, mul_one_div_cancel (by positivity : (2 * π : ℝ) ≠ 0),
    one_mul]

/-- An even real place has the symbol of the integers. -/
theorem two_pi_mul_muq_zero (t : ℝ) : 2 * π * Zeta23.ThmE.muq 0 1 t = EF.gammaBracket t := by
  rw [two_pi_mul_muq, _root_.RHTower.WeilPoleWeight.gammaBracket_eq_archimedeanWeilSymbol,
    _root_.RHTower.archimedeanWeilSymbol_div_conductor 1 one_pos t, Nat.cast_one, Real.log_one,
    sub_zero]
  exact add_comm _ _

/-- An odd real place adds `π/cosh(πt)`. -/
theorem two_pi_mul_muq_one (t : ℝ) :
    2 * π * Zeta23.ThmE.muq 1 1 t = EF.gammaBracket t + π / Real.cosh (π * t) := by
  have h0 := two_pi_mul_muq_zero t
  have hd := _root_.RHTower.re_digamma_threeQuarter_sub_quarter t
  rw [two_pi_mul_muq] at h0
  rw [two_pi_mul_muq]
  simp only [Nat.cast_one] at h0 ⊢
  linarith

theorem two_pi_mul_muq_of_le_one {κ : ℕ} (hκ : κ ≤ 1) (t : ℝ) :
    2 * π * Zeta23.ThmE.muq κ 1 t = EF.gammaBracket t + (κ : ℝ) * (π / Real.cosh (π * t)) := by
  interval_cases κ
  · rw [two_pi_mul_muq_zero, Nat.cast_zero, zero_mul, add_zero]
  · rw [two_pi_mul_muq_one, Nat.cast_one, one_mul]

/-- **The symbol of the places and of the conductor.** -/
theorem heckeSymbol_eq (ψ : HeckeCharacter 𝔪) (t : ℝ) :
    heckeSymbol 𝔪 ψ t = Real.log (heckeCompletionNorm 𝔪 : ℝ) +
      (placeDegree K : ℝ) * EF.gammaBracket t +
      (heckeConjugatePlaces 𝔪 ψ : ℝ) * (π / Real.cosh (π * t)) := by
  have hv : ∀ v : {v : InfinitePlace K // v.IsReal},
      2 * π * Zeta23.ThmE.muq (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat 1 t =
        EF.gammaBracket t +
          ((heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat : ℝ) * (π / Real.cosh (π * t)) :=
    fun v => two_pi_mul_muq_of_le_one (Bool.toNat_le _) t
  rw [heckeSymbol, two_pi_mul_muq_zero, two_pi_mul_muq_one]
  simp only [hv]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.sum_mul, placeDegree, heckeConjugatePlaces]
  push_cast
  ring

/-! ### The explicit formula on a packet -/

variable {f : ℝ → ℝ}

/-- The sum over the zeros of `L(s, ψ)` of a packet. -/
def heckeZeroSum (ψ : HeckeCharacter 𝔪) (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    (f : ℝ → ℝ) : ℝ :=
  ((heckeZeros 𝔪 ψ hψ).W cx(f) cx(f)).re

theorem heckePole_im (ψ : HeckeCharacter 𝔪) : (heckePole 𝔪 ψ).im = 0 := by
  unfold heckePole
  split_ifs
  · exact Complex.one_im
  · exact Complex.zero_im

/-- No ideal has the norm `1` among the powers of the prime ideals. -/
theorem heckeMangoldt_one (ψ : HeckeCharacter 𝔪) : heckeMangoldt 𝔪 ψ 1 = 0 := by
  rw [heckeMangoldt]
  refine Finset.sum_eq_zero fun pk hpk => ?_
  obtain ⟨P, k⟩ := pk
  obtain ⟨h1, hn⟩ := Finset.mem_filter.mp hpk
  obtain ⟨hP, hP0, hk, -⟩ := mem_primePowersLe.mp h1
  dsimp only at hn
  have h2 := two_le_absNorm_of_isPrime hP hP0
  have h3 : Ideal.absNorm P ≤ Ideal.absNorm P ^ k := Nat.le_self_pow (by omega) _
  omega

/-- The pole term of a packet: the product of its two degrees. -/
theorem re_heckePole_mul_Hfn (ψ : HeckeCharacter 𝔪) (hcont : Continuous f)
    (hfc : HasCompactSupport f) :
    (heckePole 𝔪 ψ * (Hfn (EF.weilTest cx(f) cx(f)) 0 + Hfn (EF.weilTest cx(f) cx(f)) 1)).re =
      (heckePole 𝔪 ψ).re *
        (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) := by
  have h0 : Hfn (EF.weilTest cx(f) cx(f)) 0 =
      paperFT (EF.weilTest cx(f) cx(f)) (Complex.I / 2) := by
    unfold Hfn
    congr 1
    rw [Complex.div_I]
    ring
  have h1 : Hfn (EF.weilTest cx(f) cx(f)) 1 =
      paperFT (EF.weilTest cx(f) cx(f)) (-Complex.I / 2) := by
    unfold Hfn
    congr 1
    rw [Complex.div_I]
    ring
  rw [h0, h1, Complex.mul_re, heckePole_im, zero_mul, sub_zero,
    _root_.RHTower.WeilPoleWeight.re_pole_weilTest_ofReal hcont hfc]

/-- The archimedean term of a packet: the conductor on its mass, the form of the integers once
for each unit of the degree, and the conjugate form once for each factor `Γ_ℝ(s + 1)`. -/
theorem re_heckeArch_packet (ψ : HeckeCharacter 𝔪) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ((1 / (2 * π) : ℂ) * ∫ t : ℝ, paperFT (EF.weilTest cx(f) cx(f)) t *
        ((heckeSymbol 𝔪 ψ t : ℝ) : ℂ)).re =
      Real.log (heckeCompletionNorm 𝔪 : ℝ) * packetAutocorr f 0 +
        (placeDegree K : ℝ) *
          (EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x) +
        (heckeConjugatePlaces 𝔪 ψ : ℝ) * conjugateForm f := by
  have hF : ContDiff ℝ 2 cx(f) := contDiff_ofReal_packet hf
  have hFc : HasCompactSupport cx(f) := hasCompactSupport_ofReal_packet hfc
  obtain ⟨a, -, hFs⟩ := exists_tsupport_ofReal_subset hfc
  -- the integrand is real
  have hreal : ∀ t : ℝ, paperFT (EF.weilTest cx(f) cx(f)) t * ((heckeSymbol 𝔪 ψ t : ℝ) : ℂ) =
      ((‖paperFT cx(f) t‖ ^ 2 * heckeSymbol 𝔪 ψ t : ℝ) : ℂ) := fun t => by
    rw [_root_.RHTower.paperFT_weilTest_self_ofReal hF.continuous hFc t, ← Complex.ofReal_mul]
  have hI : (∫ t : ℝ, paperFT (EF.weilTest cx(f) cx(f)) t * ((heckeSymbol 𝔪 ψ t : ℝ) : ℂ)) =
      ((∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 * heckeSymbol 𝔪 ψ t : ℝ) : ℂ) :=
    (integral_congr_ae (Eventually.of_forall hreal)).trans integral_complex_ofReal
  have hc : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hI, hc, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- the three parts of the symbol
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
  have j0 : Integrable fun t : ℝ =>
      Real.log (heckeCompletionNorm 𝔪 : ℝ) * ‖paperFT cx(f) t‖ ^ 2 := hi0.const_mul _
  have j1 : Integrable fun t : ℝ =>
      (placeDegree K : ℝ) * (‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t) := hi1.const_mul _
  have j2 : Integrable fun t : ℝ => (heckeConjugatePlaces 𝔪 ψ : ℝ) *
      (‖paperFT cx(f) t‖ ^ 2 * (π / Real.cosh (π * t))) := hi2.const_mul _
  have j01 : Integrable fun t : ℝ =>
      Real.log (heckeCompletionNorm 𝔪 : ℝ) * ‖paperFT cx(f) t‖ ^ 2 +
        (placeDegree K : ℝ) * (‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t) := j0.add j1
  have e : (fun t : ℝ => ‖paperFT cx(f) t‖ ^ 2 * heckeSymbol 𝔪 ψ t) = fun t : ℝ =>
      Real.log (heckeCompletionNorm 𝔪 : ℝ) * ‖paperFT cx(f) t‖ ^ 2 +
        (placeDegree K : ℝ) * (‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t) +
        (heckeConjugatePlaces 𝔪 ψ : ℝ) *
          (‖paperFT cx(f) t‖ ^ 2 * (π / Real.cosh (π * t))) :=
    funext fun t => by
      rw [heckeSymbol_eq]
      ring
  rw [e, integral_add j01 j2, integral_add j0 j1, integral_const_mul, integral_const_mul,
    integral_const_mul]
  -- the mass
  have hm : ∫ u, f u ^ 2 = packetAutocorr f 0 := by
    rw [packetAutocorr]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show f u ^ 2 = f u * f (u + 0)
      rw [add_zero, sq])
  have hP : 1 / (2 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 = packetAutocorr f 0 := by
    rw [_root_.RHTower.integral_norm_paperFT_sq hF hFs, integral_norm_ofReal_sq, hm]
    field_simp
  -- the form of the integers
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
  have hG : 1 / (2 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 * EF.gammaBracket t =
      EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x := by
    rw [← hweil]
    exact (_root_.RHTower.BlindPrimePowerSlack.weilArchRe_sub_pole_eq ⟨cx(f), hF, hFc⟩).symm
  -- the conjugate form
  have hS : 1 / (2 * π) * ∫ t : ℝ, ‖paperFT cx(f) t‖ ^ 2 * (π / Real.cosh (π * t)) =
      conjugateForm f := placeEnergy_eq_conjugateForm hf hfc
  linear_combination Real.log (heckeCompletionNorm 𝔪 : ℝ) * hP + (placeDegree K : ℝ) * hG +
    (heckeConjugatePlaces 𝔪 ψ : ℝ) * hS

/-- A Dirichlet series against the autocorrelation of a packet is a finite sum. -/
theorem re_tsum_coeff_packet (c : ℕ → ℂ) (hc1 : c 1 = 0) (f : ℝ → ℝ) (y : ℕ → ℝ) {Q : ℕ}
    (hQ : ∀ n : ℕ, Q < n → packetAutocorr f (y n) = 0) :
    (∑' n : ℕ, c n / ((Real.sqrt n : ℝ) : ℂ) * EF.weilTest cx(f) cx(f) (y n)).re =
      ∑ k ∈ Icc 2 Q, (c k).re / Real.sqrt k * packetAutocorr f (y k) := by
  have hk : ∀ x : ℝ, EF.weilTest cx(f) cx(f) x = ((packetAutocorr f x : ℝ) : ℂ) := fun x =>
    weilTest_packet f x
  rw [tsum_eq_sum (s := Icc 2 Q) (fun n hn => ?_), Complex.re_sum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [hk, show c n / ((Real.sqrt n : ℝ) : ℂ) * ((packetAutocorr f (y n) : ℝ) : ℂ) =
      ((packetAutocorr f (y n) / Real.sqrt n : ℝ) : ℂ) * c n by
        push_cast
        ring, Complex.re_ofReal_mul]
    ring
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · have h01 : n = 0 ∨ n = 1 := by omega
      rcases h01 with rfl | rfl
      · rw [Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, div_zero, zero_mul]
      · rw [hc1, zero_div, zero_mul]
    · rw [hk, hQ n h, Complex.ofReal_zero, mul_zero]

/-- **Weil's form of a Hecke character on a packet, through the autocorrelation.** -/
def heckePacketForm (ψ : HeckeCharacter 𝔪) (Q : ℕ) (g : ℝ → ℝ) : ℝ :=
  (heckePole 𝔪 ψ).re *
      (2 * ((∫ u, g u * Real.exp (-u / 2)) * ∫ u, g u * Real.exp (u / 2))) +
    Real.log (heckeCompletionNorm 𝔪 : ℝ) * packetAutocorr g 0 +
    (placeDegree K : ℝ) *
      (EF.gammaBracket 0 * packetAutocorr g 0 + ∫ x in Set.Ioi 0, levyJump g x) +
    (heckeConjugatePlaces 𝔪 ψ : ℝ) * conjugateForm g -
    2 * ∑ k ∈ Icc 2 Q, (heckeMangoldt 𝔪 ψ k).re / Real.sqrt k * packetAutocorr g (Real.log k)

/-- **The explicit formula of `L(s, ψ)` on a packet.** -/
theorem heckeZeroSum_eq_heckePacketForm (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {Q : ℕ} (hQ : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0) :
    heckeZeroSum 𝔪 ψ hψ f = heckePacketForm 𝔪 ψ Q f := by
  have hF : ContDiff ℝ 2 cx(f) := contDiff_ofReal_packet hf
  have hFc : HasCompactSupport cx(f) := hasCompactSupport_ofReal_packet hfc
  have hEF := W_heckeZeros_eq 𝔪 ψ hψ hF hFc hF hFc
  have hQ' : ∀ n : ℕ, Q < n → packetAutocorr f (-Real.log n) = 0 := fun n hn => by
    rw [packetAutocorr_neg]
    exact hQ n hn
  have hp1 : (∑' n : ℕ, heckeMangoldt 𝔪 ψ n / ((Real.sqrt n : ℝ) : ℂ) *
        EF.weilTest cx(f) cx(f) (Real.log n)).re =
      ∑ k ∈ Icc 2 Q, (heckeMangoldt 𝔪 ψ k).re / Real.sqrt k * packetAutocorr f (Real.log k) :=
    re_tsum_coeff_packet (heckeMangoldt 𝔪 ψ) (heckeMangoldt_one 𝔪 ψ) f (fun n => Real.log n) hQ
  have hp2 : (∑' n : ℕ, conj (heckeMangoldt 𝔪 ψ n) / ((Real.sqrt n : ℝ) : ℂ) *
        EF.weilTest cx(f) cx(f) (-Real.log n)).re =
      ∑ k ∈ Icc 2 Q, (heckeMangoldt 𝔪 ψ k).re / Real.sqrt k * packetAutocorr f (Real.log k) := by
    have h := re_tsum_coeff_packet (fun n => conj (heckeMangoldt 𝔪 ψ n)) (by
      show conj (heckeMangoldt 𝔪 ψ 1) = 0
      rw [heckeMangoldt_one, map_zero]) f (fun n => -Real.log n) hQ'
    simp only [Complex.conj_re, packetAutocorr_neg] at h
    exact h
  rw [heckeZeroSum, hEF, Complex.sub_re, Complex.sub_re, Complex.add_re,
    re_heckePole_mul_Hfn 𝔪 ψ hf.continuous hfc, re_heckeArch_packet 𝔪 ψ hf hfc, hp1, hp2,
    heckePacketForm]
  ring

/-! ### The pairing of the ideals at finite scale -/

/-- The weighted contacts of a packet in a window tend to the contacts of its autocorrelation. -/
theorem tendsto_weightedContact_window (w : ℕ → ℝ) (hcont : Continuous f) {K₀ : ℕ}
    (hK : 1 ≤ K₀) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K₀ ≤ u → f u = 0) :
    Tendsto (weightedContact w f (3 * K₀)) atTop
      (𝓝 (∑ k ∈ Icc 2 (3 * K₀), w k / Real.sqrt k * packetAutocorr f (Real.log k))) := by
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsuppW := window_of_support hK hsupp
  have h := tendsto_weightedContact w hcont (L := 3 * K₀) (by omega)
  have hsum : ∑ k ∈ Icc 2 (3 * K₀), w k / Real.sqrt k *
        ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K₀ : ℕ) : ℝ)), f u * f (u + Real.log k) =
      ∑ k ∈ Icc 2 (3 * K₀), w k / Real.sqrt k * packetAutocorr f (Real.log k) :=
    Finset.sum_congr rfl fun k _ => by
      rw [packetAutocorr_eq_integral_window hδ hsuppW]
  rw [hsum] at h
  exact h

/-- The pairing of the ideals of `K` twisted by `ψ`, counted by their norms, without the
contacts: `d` times the jets and the counterterm of the integers, minus the conjugate jets of the
factors `Γ_ℝ(s + 1)`, minus `log N` times the mass. -/
def heckeForm (ψ : HeckeCharacter 𝔪) (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  (placeDegree K : ℝ) * degreeForm f L N -
    (heckeConjugatePlaces 𝔪 ψ : ℝ) * conjugateJet f L N -
    Real.log (heckeCompletionNorm 𝔪 : ℝ) *
      ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n

/-- **The pairing of the ideals of a number ring weighs the zeros of its Hecke functions.** For
a primitive ray class character `ψ` of a number field and a packet in a window: the jets of the
places, the counterterm, and twice the contacts `Re Λ_ψ` of the ideals tend to the pole plane
`m_ψ 2d₁d₂` minus the sum over the zeros of `L(s, ψ)`. -/
theorem tendsto_heckeForm_add_idealContact (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {K₀ : ℕ} (hK : 1 ≤ K₀) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K₀ ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => heckeForm 𝔪 ψ f (3 * K₀) N +
        2 * weightedContact (fun n => (heckeMangoldt 𝔪 ψ n).re) f (3 * K₀) N) atTop
      (𝓝 ((heckePole 𝔪 ψ).re *
          (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) -
        heckeZeroSum 𝔪 ψ hψ f)) := by
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsuppW := window_of_support hK hsupp
  have h1L : (0 : ℝ) < 1 + ((3 * K₀ : ℕ) : ℝ) := by positivity
  have hQ : ∀ n : ℕ, 3 * K₀ < n → packetAutocorr f (Real.log n) = 0 := fun n hn =>
    packetAutocorr_eq_zero_of_window hδ hsuppW (Real.log_le_log h1L (by
      have : ((3 * K₀ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith))
  -- the jets of the integers
  obtain ⟨R, hsuppR⟩ := exists_natCast_le_abs_imp_eq_zero hfc
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfc (by norm_num)
  have hB' : ∀ u, |f u| ≤ B := fun u => by
    rw [← Real.norm_eq_abs]
    exact hB u
  have hLip : ∀ u v, |f u - f v| ≤ (C : ℝ) * |u - v| := fun u v => by
    have h := hC.dist_le_mul u v
    rwa [Real.dist_eq, Real.dist_eq] at h
  have h1 : Tendsto (degreeForm f (3 * K₀)) atTop
      (𝓝 (-(EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x))) := by
    rw [← weilArchRe_sub_pole_packet hf hfc hsuppR hB' hLip]
    exact tendsto_degreeForm hf hfc hK hsupp
  -- the contacts of the ideals
  have h2 : Tendsto (weightedContact (fun n => (heckeMangoldt 𝔪 ψ n).re) f (3 * K₀)) atTop
      (𝓝 (∑ k ∈ Icc 2 (3 * K₀),
        (heckeMangoldt 𝔪 ψ k).re / Real.sqrt k * packetAutocorr f (Real.log k))) :=
    tendsto_weightedContact_window _ hf.continuous hK hsupp
  -- the conjugate jets and the mass
  have h3 : Tendsto (conjugateJet f (3 * K₀)) atTop (𝓝 (conjugateForm f)) := by
    rw [← integral_window_conjugate hf.continuous hfc hδ hsuppW]
    exact tendsto_conjugateJet hf.continuous (3 * K₀)
  have h4 := tendsto_degreeMass hf.continuous hK hsupp
  have hlim := (((h1.const_mul (placeDegree K : ℝ)).sub
    (h3.const_mul (heckeConjugatePlaces 𝔪 ψ : ℝ))).sub
    (h4.const_mul (Real.log (heckeCompletionNorm 𝔪 : ℝ)))).add (h2.const_mul 2)
  have hm : ∫ u, f u ^ 2 = packetAutocorr f 0 := by
    rw [packetAutocorr]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show f u ^ 2 = f u * f (u + 0)
      rw [add_zero, sq])
  have e : (heckePole 𝔪 ψ).re *
        (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) -
      heckeZeroSum 𝔪 ψ hψ f =
      (placeDegree K : ℝ) *
          -(EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x) -
        (heckeConjugatePlaces 𝔪 ψ : ℝ) * conjugateForm f -
        Real.log (heckeCompletionNorm 𝔪 : ℝ) * (∫ u, f u ^ 2) +
        2 * ∑ k ∈ Icc 2 (3 * K₀),
          (heckeMangoldt 𝔪 ψ k).re / Real.sqrt k * packetAutocorr f (Real.log k) := by
    rw [heckeZeroSum_eq_heckePacketForm 𝔪 ψ hψ hf hfc hQ, heckePacketForm, hm]
    ring
  rw [e]
  refine hlim.congr fun N => ?_
  rw [heckeForm]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
