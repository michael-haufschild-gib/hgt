import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexOfAVirtualConfigurationCountsItsZerosAndItsPoles
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormOnStepPacketsIsTheChargesAPotentialAndADirichletForm
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheMatrixOfAStepPacketIsTheMixedDifferenceOfItsWindows
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic
import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm
import GaloisForLFunctions.SquareRootThreshold.ZetaSmallApertureHeightWindowPositivity
import GaloisForLFunctions.RHTower.WeilMarkovOneBoundState

/-!
# The neutral part is Weil's form of the zeros minus the poles

Weil's form of a packet is twice the product of its two charges plus a neutral part: the
archimedean form minus the contacts (`neutralForm`, `neutralForm_eq`). The product of the charges
is Weil's form of the two poles `s = 0` and `s = 1` of the completed zeta function
(`poleConfig`, `poleConfig_W_ofReal`). So the neutral part is the form of a divisor, the zeros
minus the poles:

* on smooth packets it is `W_ζ − W_poles` (`neutralForm_eq_re_sub`), the archimedean-minus-prime
  energy `markovEnergy` (`neutralForm_eq_markovEnergy`);
* on step packets it is the neutral part of the block matrix: density, jets and contacts
  (`neutralForm_stepPacket`).

The index law of a virtual configuration counts a zero and a pole right of the line alike. The
pole `s = 1` is right of the line, so:

* the largest number of negative squares of the neutral form on a family of tests is one plus
  the number of zeros right of the line (`exists_le_negIndex_neutralGram_iff`); one negative
  square is always there (`exists_one_le_negIndex_neutralGram`); the same law holds for every
  tempered configuration that does not contain the point `1`
  (`exists_le_negIndex_sub_poleConfig_iff`);
* the Riemann hypothesis holds iff the neutral form has at most one negative square on every
  family (`riemannHypothesis_iff_forall_negIndex_neutralGram_le_one`): the signature of an
  intersection form on a surface. This is the one-bound-state law of the archimedean-minus-prime
  energy (`RHTower.riemannHypothesis_iff_not_exists_negDef_markovPlane`), here with the count of
  the squares.
-/

open Complex Matrix Finset MeasureTheory
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri

/-! ### The configuration of the two poles -/

/-- The two poles `s = 0` and `s = 1` of the completed zeta function, as a configuration closed
under `ρ ↦ 1 − ρ̄`. -/
def poleConfig : ZeroConfig where
  carrier := (({0, 1} : Finset ℂ) : Set ℂ)
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := fun ρ hρ => by
    have h : ρ = 0 ∨ ρ = 1 := by simpa using hρ
    rcases h with rfl | rfl <;> simp
  reflect_mem := fun ρ hρ => by
    have h : ρ = 0 ∨ ρ = 1 := by simpa using hρ
    rcases h with rfl | rfl <;> simp [reflect]
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => (Finset.finite_toSet _).subset Set.inter_subset_left

theorem mem_poleConfig {ρ : ℂ} : ρ ∈ poleConfig.carrier ↔ ρ = 0 ∨ ρ = 1 := by
  show ρ ∈ (({0, 1} : Finset ℂ) : Set ℂ) ↔ _
  simp

theorem poleConfig_mult (ρ : ℂ) : poleConfig.mult ρ = 1 := rfl

theorem temperedConfig_poleConfig : TemperedConfig poleConfig := by
  haveI : Finite poleConfig.carrier := (Finset.finite_toSet _).to_subtype
  exact Summable.of_finite

/-- **Weil's form of the poles**: `h_f(i/2) conj h_g(−i/2) + h_f(−i/2) conj h_g(i/2)`. -/
theorem poleConfig_W (f g : ℝ → ℂ) :
    poleConfig.W f g =
      paperFT f (I / 2) * conj (paperFT g (-I / 2)) +
        paperFT f (-I / 2) * conj (paperFT g (I / 2)) := by
  have hγ0 : gammaOf 0 = I / 2 := by
    have h : (I / 2 : ℂ) * I = -1 / 2 := by rw [div_mul_eq_mul_div, I_mul_I]
    rw [gammaOf, div_eq_iff I_ne_zero, h]
    norm_num
  have hγ1 : gammaOf 1 = -I / 2 := by
    have h : (-I / 2 : ℂ) * I = 1 / 2 := by rw [div_mul_eq_mul_div, neg_mul, I_mul_I, neg_neg]
    rw [gammaOf, div_eq_iff I_ne_zero, h]
    norm_num
  have hc0 : conj (I / 2 : ℂ) = -I / 2 := by rw [map_div₀, conj_I, map_ofNat]
  have hc1 : conj (-I / 2 : ℂ) = I / 2 := by rw [map_div₀, map_neg, conj_I, neg_neg, map_ofNat]
  show ∑' ρ : (({0, 1} : Finset ℂ) : Set ℂ), poleConfig.Wsummand f g ρ = _
  rw [Finset.tsum_subtype' ({0, 1} : Finset ℂ) (poleConfig.Wsummand f g),
    Finset.sum_pair zero_ne_one]
  simp only [ZeroConfig.Wsummand, poleConfig_mult, hγ0, hγ1, hc0, hc1, Nat.cast_one, one_mul]

/-- **On a real packet the form of the poles is twice the product of the two charges.** -/
theorem poleConfig_W_ofReal (f : ℝ → ℝ) :
    poleConfig.W (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) =
      ((2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) : ℝ) : ℂ) := by
  rw [poleConfig_W, _root_.RHTower.WeilLevyPole.paperFT_ofReal_I_div_two,
    _root_.RHTower.WeilLevyPole.paperFT_ofReal_neg_I_div_two, Complex.conj_ofReal,
    Complex.conj_ofReal]
  push_cast
  ring

/-- The form of the poles is the pole term of Weil's functional. -/
theorem poleConfig_W_eq_weilPoleTerm {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    poleConfig.W f f = _root_.RHTower.weilPoleTerm (EF.weilTest f f) := by
  rw [poleConfig_W, _root_.RHTower.weilPoleTerm_weilTest_eq hf hfc]

/-- **The form of the zeros minus the poles is the archimedean-minus-prime energy.** -/
theorem re_W_sub_poleConfig_W_eq_markovEnergy {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (zetaZeroConfig.W f f - poleConfig.W f f).re = _root_.RHTower.markovEnergy f := by
  rw [_root_.RHTower.markovEnergy_eq_W_sub hf hfc, Complex.sub_re,
    poleConfig_W_eq_weilPoleTerm hf.continuous hfc]

/-! ### The neutral part of Weil's form of a packet -/

/-- The neutral part of Weil's form of a packet: the form without the product of the two
charges. -/
def neutralForm (Q : ℕ) (g : ℝ → ℝ) : ℝ :=
  packetForm Q g - 2 * ((∫ u, g u * Real.exp (-u / 2)) * ∫ u, g u * Real.exp (u / 2))

/-- The neutral part is the archimedean form minus the contacts. -/
theorem neutralForm_eq (Q : ℕ) (g : ℝ → ℝ) :
    neutralForm Q g =
      EF.gammaBracket 0 * packetAutocorr g 0 + (∫ x in Set.Ioi 0, levyJump g x) -
        2 * ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr g (Real.log k) := by
  unfold neutralForm packetForm
  ring

/-- **On smooth packets the neutral part is the form of the zeros minus the form of the
poles.** -/
theorem neutralForm_eq_re_sub {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {Q : ℕ} (hQ : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0) :
    neutralForm Q f =
      (zetaZeroConfig.W (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) -
        poleConfig.W (fun u => (f u : ℂ)) (fun u => (f u : ℂ))).re := by
  rw [neutralForm, ← zeroSum_eq_packetForm hf hfc hQ, Complex.sub_re, poleConfig_W_ofReal,
    Complex.ofReal_re]
  rfl

/-- On smooth packets the neutral part is the archimedean-minus-prime energy. -/
theorem neutralForm_eq_markovEnergy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {Q : ℕ}
    (hQ : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0) :
    neutralForm Q f = _root_.RHTower.markovEnergy fun u => (f u : ℂ) := by
  rw [neutralForm_eq_re_sub hf hfc hQ,
    re_W_sub_poleConfig_W_eq_markovEnergy (contDiff_ofReal_packet hf)
      (hasCompactSupport_ofReal_packet hfc)]

/-- The second charge of a step packet is the sum of its values. -/
theorem integral_stepPacket_mul_exp {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    ∫ u, stepPacket R J σ u * Real.exp (u / 2) = ∑ j ∈ range J, σ j := by
  have hint : ∀ j ∈ range J, Integrable fun u =>
      σ j * (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u * Real.exp (u / 2)) :=
    fun j _ => (integrable_flatPacket_mul _ _ (by fun_prop)).const_mul (σ j)
  have h : (fun u => stepPacket R J σ u * Real.exp (u / 2)) = fun u => ∑ j ∈ range J,
      σ j * (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u * Real.exp (u / 2)) := by
    funext u
    rw [stepPacket, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_flatPacket_mul_exp
    (by exact_mod_cast (by omega : 0 < R + j))
    (by exact_mod_cast (by omega : R + j ≤ R + (j + 1)))]
  push_cast
  ring

/-- The first charge of a step packet is the sum of its values against the degrees of the
blocks. -/
theorem integral_stepPacket_mul_exp_neg {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    ∫ u, stepPacket R J σ u * Real.exp (-u / 2) = ∑ j ∈ range J, σ j * blockDegree (R + j) := by
  have hint : ∀ j ∈ range J, Integrable fun u =>
      σ j * (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u * Real.exp (-u / 2)) :=
    fun j _ => (integrable_flatPacket_mul _ _ (by fun_prop)).const_mul (σ j)
  have h : (fun u => stepPacket R J σ u * Real.exp (-u / 2)) = fun u => ∑ j ∈ range J,
      σ j * (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u * Real.exp (-u / 2)) := by
    funext u
    rw [stepPacket, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_flatPacket_mul_exp_neg
    (by exact_mod_cast (by omega : 0 < R + j))
    (by exact_mod_cast (by omega : R + j ≤ R + (j + 1)))]
  rfl

/-- **On step packets the neutral part is the neutral part of the block matrix.** -/
theorem neutralForm_stepPacket {R : ℕ} (hR : 1 ≤ R) (Q J : ℕ) (σ : ℕ → ℝ) :
    neutralForm Q (stepPacket R J σ) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) := by
  rw [neutralForm, packetForm_stepPacket_eq_sum_blockMatrix hR,
    sum_blockMatrix_eq_charges_add_neutral, integral_stepPacket_mul_exp_neg hR,
    integral_stepPacket_mul_exp hR]
  ring

/-! ### The index of the neutral form -/

theorem extMult_poleConfig_of_mem {ρ : ℂ} (h : ρ = 0 ∨ ρ = 1) : extMult poleConfig ρ = 1 := by
  rw [extMult, if_pos (mem_poleConfig.mpr h), poleConfig_mult]

theorem extMult_poleConfig_of_notMem {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    extMult poleConfig ρ = 0 := by
  rw [extMult, if_neg fun h => (mem_poleConfig.mp h).elim h0 h1]

/-- **The defect points of a configuration minus the poles**: its points right of the line and
the pole `s = 1`, if the configuration does not contain the point `1`. -/
theorem virtualDefect_poleConfig (A : ZeroConfig) (h1 : (1 : ℂ) ∉ A.carrier) :
    virtualDefect A poleConfig = insert 1 (rightZeros A) := by
  ext ρ
  constructor
  · rintro (⟨hre, hne⟩ | ⟨hre, hlt⟩)
    · by_cases hρ1 : ρ = 1
      · exact Or.inl hρ1
      · refine Or.inr ⟨?_, hre⟩
        by_contra hmem
        apply hne
        have h0 : ρ ≠ 0 := by
          rintro rfl
          norm_num at hre
        rw [extMult_poleConfig_of_notMem h0 hρ1, extMult, if_neg hmem]
    · exfalso
      have h0 : ρ ≠ 0 := by
        rintro rfl
        norm_num at hre
      have hρ1 : ρ ≠ 1 := by
        rintro rfl
        norm_num at hre
      rw [extMult_poleConfig_of_notMem h0 hρ1] at hlt
      exact Nat.not_lt_zero _ hlt
  · rintro (rfl | ⟨hmem, hre⟩)
    · refine Or.inl ⟨by norm_num, ?_⟩
      rw [extMult_poleConfig_of_mem (Or.inr rfl), extMult, if_neg h1]
      exact zero_ne_one
    · refine Or.inl ⟨hre, ?_⟩
      have h0 : ρ ≠ 0 := by
        rintro rfl
        norm_num at hre
      have hρ1 : ρ ≠ 1 := by
        rintro rfl
        exact h1 hmem
      rw [extMult_poleConfig_of_notMem h0 hρ1, extMult, if_pos hmem]
      exact Nat.one_le_iff_ne_zero.mp (A.one_le_mult ρ hmem)

/-- **The index law of a configuration minus the poles.** The form `W_A − W_poles` has `n`
negative squares on some family of `n` tests iff `n` is at most one plus the number of points
of `A` right of the line. -/
theorem exists_le_negIndex_sub_poleConfig_iff (A : ZeroConfig) (hA : TemperedConfig A)
    (h1 : (1 : ℂ) ∉ A.carrier) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (zeroGram A f - zeroGram poleConfig f)) ↔
      (n : ℕ∞) ≤ (rightZeros A).encard + 1 := by
  rw [exists_le_negIndex_sub_zeroGram_iff A poleConfig hA temperedConfig_poleConfig,
    virtualDefect_poleConfig A h1, Set.encard_insert_of_notMem fun h => h1 h.1]

/-- **A configuration has no point right of the line iff its form minus the form of the poles
has at most one negative square** on every family of tests. -/
theorem rightZeros_eq_empty_iff_forall_negIndex_sub_poleConfig_le_one (A : ZeroConfig)
    (hA : TemperedConfig A) (h1 : (1 : ℂ) ∉ A.carrier) :
    rightZeros A = ∅ ↔ ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
      (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (zeroGram A f - zeroGram poleConfig f) ≤ 1 := by
  constructor
  · intro hempty n f hf hfc
    have hle := negIndex_sub_zeroGram_le_virtualDefect A poleConfig hA temperedConfig_poleConfig
      f hf hfc
    rw [virtualDefect_poleConfig A h1, Set.encard_insert_of_notMem fun h => h1 h.1, hempty,
      Set.encard_empty, zero_add] at hle
    exact_mod_cast hle
  · intro h
    by_contra hne
    -- a point right of the line and the pole give two negative squares
    have h1' : (1 : ℕ∞) ≤ (rightZeros A).encard :=
      Set.one_le_encard_iff_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr hne)
    have h11 : ((2 : ℕ) : ℕ∞) = 1 + 1 := by
      rw [Nat.cast_ofNat]
      exact one_add_one_eq_two.symm
    have h2 : ((2 : ℕ) : ℕ∞) ≤ (rightZeros A).encard + 1 := by
      rw [h11]
      exact add_le_add h1' le_rfl
    obtain ⟨f, hf, hfc, hn⟩ := (exists_le_negIndex_sub_poleConfig_iff A hA h1 2).mpr h2
    have := h 2 f hf hfc
    omega

/-- The point `1` is not a zero of the zeta function. -/
theorem one_notMem_zetaZeroConfig : (1 : ℂ) ∉ zetaZeroConfig.carrier := fun h => by
  have h' : IsNontrivialZero (1 : ℂ) := h
  have h2 := h'.2.2
  norm_num at h2

/-- **The index law of the neutral form.** It has `n` negative squares on some family of `n`
tests iff `n` is at most one plus the number of zeros right of the line. -/
theorem exists_le_negIndex_neutralGram_iff (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (zeroGram zetaZeroConfig f - zeroGram poleConfig f)) ↔
      (n : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard + 1 :=
  exists_le_negIndex_sub_poleConfig_iff zetaZeroConfig temperedConfig_zetaZeroConfig
    one_notMem_zetaZeroConfig n

/-- **The pole is one negative square of the neutral form.** -/
theorem exists_one_le_negIndex_neutralGram :
    ∃ f : Fin 1 → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      1 ≤ hermNegIndex (zeroGram zetaZeroConfig f - zeroGram poleConfig f) :=
  (exists_le_negIndex_neutralGram_iff 1).mpr (by
    rw [Nat.cast_one]
    exact le_add_self)

/-- **The Riemann hypothesis is the signature of the neutral form**: it holds iff the form of
the zeros minus the poles has at most one negative square on every family of tests. -/
theorem riemannHypothesis_iff_forall_negIndex_neutralGram_le_one :
    RiemannHypothesis ↔ ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
      (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (zeroGram zetaZeroConfig f - zeroGram poleConfig f) ≤ 1 := by
  rw [← rightZeros_zeta_eq_empty_iff]
  exact rightZeros_eq_empty_iff_forall_negIndex_sub_poleConfig_le_one zetaZeroConfig
    temperedConfig_zetaZeroConfig one_notMem_zetaZeroConfig

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
