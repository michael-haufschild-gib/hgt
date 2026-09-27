import GaloisForLFunctions.RHTower.MobiusPrimeInsertionLiteralPackets
import GaloisForLFunctions.RHTower.MobiusCubicSourceMertensEnergy

/-!
# Macroscopic aligned prime packets under insertion

A fixed finite central packet `B_ε = f_3 - f_(3(1+ε)) + f_6 - f_(6(1+ε))` is uniformly (in
`0 ≤ δ ≤ δ₀`) within `O(ε²)` of `-ε (v_3 + v_6)`, so for small fixed `ε` its insertion `D_2 B_ε`
has norm below `0.888 ‖B_ε‖`.  Selecting `≫ R/log R` primes from four narrow bands at scale `R`
produces literal Möbius tuples each within `τ ‖B_ε‖` of the dilated central packet; any sum of
them keeps the insertion ratio below `4/5`, and has energy `≫ M² R^(-1-δ)`.  The unconditional
Mertens saving then forces the actual complement of the selected packet in the full source to be
asymptotically antiparallel to it, and a literal half-scale prime band removes more than a third
of the inserted energy.
-/

open Filter Topology Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.CubicGamma

/-! ### The central packet -/

/-- The finite central packet `B_ε = f_3 - f_(3(1+ε)) + f_6 - f_(6(1+ε))`. -/
def centralPacket (ε : ℝ) : ℝ → ℝ := twoDipolePrecursor 3 (3 * (1 + ε)) 6 (6 * (1 + ε))

/-- The central first-jet profile `V = v_3 + v_6`. -/
def centralProfile (t : ℝ) : ℝ := jetProfile 3 t + jetProfile 6 t

theorem gammaFinite_centralPacket {δ : ℝ} (hδ : 0 < 5 + δ) {ε : ℝ} (hε : 0 ≤ ε) :
    GammaFinite δ (centralPacket ε) :=
  gammaFinite_twoDipolePrecursor hδ (by norm_num) (by positivity) (by norm_num) (by positivity)

theorem gammaFinite_centralProfile {δ : ℝ} (hδ : 0 < 5 + δ) : GammaFinite δ centralProfile :=
  (gammaFinite_jetProfile hδ (by norm_num)).add (gammaFinite_jetProfile hδ (by norm_num))

theorem insertTwo_centralProfile :
    insertTwo centralProfile = fun t => jetProfile 3 t - jetProfile 12 t := by
  funext t
  have h := dyadic_insertion_telescopes 3 t
  unfold insertTwo centralProfile
  norm_num at h ⊢
  exact h

/-- `‖B_ε/ε + V‖_δ ≤ 4 C_2 ε` for `0 < ε ≤ 1`, `0 ≤ δ ≤ 1`. -/
theorem gammaNorm_centralPacket_approx {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    gammaNorm δ (fun t => centralPacket ε t / ε + centralProfile t) ≤ 4 * jetConst 2 * ε := by
  have hδ : 0 < 5 + δ := by linarith
  have hC2 := jetConst_nonneg 2
  have e : (fun t => centralPacket ε t / ε + centralProfile t) =
      fun t => ((atom 3 t - atom (3 * (1 + ε)) t) / ε + jetProfile 3 t) +
        ((atom 6 t - atom (6 * (1 + ε)) t) / ε + jetProfile 6 t) := by
    funext t; unfold centralPacket centralProfile twoDipolePrecursor; ring
  have fin : ∀ y : ℝ, 0 < y → GammaFinite δ
      (fun t => (atom y t - atom (y * (1 + ε)) t) / ε + jetProfile y t) := by
    intro y hy
    have := (((gammaFinite_atom hδ hy).sub (gammaFinite_atom hδ (by positivity : 0 < y * (1 + ε)))).smul
      ε⁻¹).add (gammaFinite_jetProfile hδ hy)
    refine this.congr ?_; funext t; ring
  have bnd : ∀ y : ℝ, 1 ≤ y → gammaNorm δ
      (fun t => (atom y t - atom (y * (1 + ε)) t) / ε + jetProfile y t) ≤ 2 * jetConst 2 * ε := by
    intro y hy
    have h := gammaNorm_dipole_div_add_le hδ0 hδ1 (x := y) (y := y) (e := ε) (by linarith) le_rfl
      hε.le hε1 hε
    rw [div_self hε.ne', sub_self, abs_zero, zero_mul, add_zero, sub_self, zero_mul, add_zero] at h
    have hp : y ^ (-(1 + δ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
    have hp0 : 0 ≤ y ^ (-(1 + δ) / 2) := by positivity
    refine h.trans ?_
    have : 2 * jetConst 2 * y ^ (-(1 + δ) / 2) * ε ^ 2 / ε = 2 * jetConst 2 * y ^ (-(1 + δ) / 2) * ε := by
      field_simp
    rw [this]
    calc 2 * jetConst 2 * y ^ (-(1 + δ) / 2) * ε ≤ 2 * jetConst 2 * 1 * ε := by gcongr
      _ = 2 * jetConst 2 * ε := by ring
  rw [e]
  refine (gammaNorm_add_le hδ (fin 3 (by norm_num)) (fin 6 (by norm_num))).trans ?_
  have := bnd 3 (by norm_num)
  have := bnd 6 (by norm_num)
  linarith

/-- `‖D_2 B_ε/ε + D_2 V‖_δ ≤ 8 C_2 ε`. -/
theorem gammaNorm_insertTwo_centralPacket_approx {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    gammaNorm δ (fun t => insertTwo (centralPacket ε) t / ε + insertTwo centralProfile t) ≤
      8 * jetConst 2 * ε := by
  have hδ : 0 < 5 + δ := by linarith
  have e : (fun t => insertTwo (centralPacket ε) t / ε + insertTwo centralProfile t) =
      insertTwo (fun t => centralPacket ε t / ε + centralProfile t) := by
    funext t; unfold insertTwo dilate; ring
  rw [e]
  have hfin : GammaFinite δ (fun t => centralPacket ε t / ε + centralProfile t) := by
    have := ((gammaFinite_centralPacket hδ hε.le).smul ε⁻¹).add (gammaFinite_centralProfile hδ)
    refine this.congr ?_; funext t; ring
  refine (gammaNorm_insertTwo_le hδ0 hfin).trans ?_
  have := gammaNorm_centralPacket_approx hδ0 hδ1 hε hε1
  linarith

/-! ### Uniform bounds on the central profiles -/

private theorem gram_one_one_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    3 / 128 ≤ abelPrefixGramKernel δ 1 1 := by
  unfold abelPrefixGramKernel abelPrefixGramNumerator abelPrefixGramCore
  have h2 : (1 + 1 : ℝ) ^ (7 + δ) ≤ 2 ^ (8 : ℝ) := by
    rw [show (1 + 1 : ℝ) = 2 by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2' : (2 : ℝ) ^ (8 : ℝ) = 256 := by norm_num
  have hpos : 0 < (1 + 1 : ℝ) ^ (7 + δ) := by positivity
  rw [h2'] at h2
  have hnum : 6 ≤ (6 + 2 * δ) * (3 * 1 * 1 - 1 ^ 2 - 1 ^ 2) + δ * (1 + δ) * (1 * 1) := by nlinarith
  rw [show 1 * 1 / (1 + 1 : ℝ) ^ (7 + δ) * ((6 + 2 * δ) * (3 * 1 * 1 - 1 ^ 2 - 1 ^ 2) +
    δ * (1 + δ) * (1 * 1)) = ((6 + 2 * δ) * (3 * 1 * 1 - 1 ^ 2 - 1 ^ 2) + δ * (1 + δ) * (1 * 1)) /
      (1 + 1 : ℝ) ^ (7 + δ) by ring]
  rw [le_div_iff₀ hpos]
  have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 3 / 128)
  linarith

/-- `‖v_3 + v_6‖_δ² ≥ 1/384` for `0 ≤ δ ≤ 1`. -/
theorem gammaEnergy_centralProfile_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 / 384 ≤ gammaEnergy δ centralProfile := by
  have e : centralProfile = dilate 3 (fun t => jetProfile 1 t + 1 * jetProfile 2 t) := by
    rw [dilate_add_fun, dilate_smul_fun, dilate_jetProfile, dilate_jetProfile]
    funext t; unfold centralProfile; norm_num
  rw [e, gammaEnergy_dilate (by norm_num), gammaEnergy_jet_combo hδ0 one_pos two_pos]
  have g11 := gram_one_one_ge hδ0 hδ1
  have g12 : 0 < abelPrefixGramKernel δ 1 2 :=
    abelPrefixGramKernel_pos_of_comparable hδ0 one_pos two_pos (by norm_num) (by norm_num)
  have g22 : 0 < abelPrefixGramKernel δ 2 2 :=
    abelPrefixGramKernel_pos_of_comparable hδ0 two_pos two_pos (by norm_num) (by norm_num)
  have h3 : (1 : ℝ) / 9 ≤ (3 : ℝ) ^ (-1 - δ) := by
    rw [show (1 : ℝ) / 9 = 3 ^ (-2 : ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsum : 3 / 128 ≤ 1 * 1 * abelPrefixGramKernel δ 1 1 + 2 * 1 * (1 * 2 * abelPrefixGramKernel δ 1 2)
      + 1 ^ 2 * (2 * 2 * abelPrefixGramKernel δ 2 2) := by nlinarith
  have := mul_le_mul h3 hsum (by norm_num) (by positivity)
  linarith

/-- `‖v_3 - v_12‖_δ² ≥ 1/384` for `0 ≤ δ ≤ 1`. -/
theorem gammaEnergy_insertTwo_centralProfile_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 / 384 ≤ gammaEnergy δ (insertTwo centralProfile) := by
  have e : insertTwo centralProfile = dilate 3 (fun t => jetProfile 1 t + (-1) * jetProfile 4 t) := by
    rw [insertTwo_centralProfile, dilate_add_fun, dilate_smul_fun, dilate_jetProfile,
      dilate_jetProfile]
    funext t; norm_num; ring
  rw [e, gammaEnergy_dilate (by norm_num), gammaEnergy_jet_combo hδ0 one_pos (by norm_num)]
  have g11 := gram_one_one_ge hδ0 hδ1
  have g14 : abelPrefixGramKernel δ 1 4 < 0 :=
    abelPrefixGramKernel_neg_of_separated (x := 4) (y := 1) hδ0 hδ1 one_pos (by norm_num) |>
      fun h => by rw [show abelPrefixGramKernel δ 1 4 = abelPrefixGramKernel δ 4 1 by
        unfold abelPrefixGramKernel abelPrefixGramNumerator abelPrefixGramCore; ring_nf]; exact h
  have g44 : 0 < abelPrefixGramKernel δ 4 4 :=
    abelPrefixGramKernel_pos_of_comparable hδ0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : (1 : ℝ) / 9 ≤ (3 : ℝ) ^ (-1 - δ) := by
    rw [show (1 : ℝ) / 9 = 3 ^ (-2 : ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsum : 3 / 128 ≤ 1 * 1 * abelPrefixGramKernel δ 1 1 +
      2 * (-1) * (1 * 4 * abelPrefixGramKernel δ 1 4) +
      (-1) ^ 2 * (4 * 4 * abelPrefixGramKernel δ 4 4) := by nlinarith
  have := mul_le_mul h3 hsum (by norm_num) (by positivity)
  linarith

theorem one_div_twenty_le_gammaNorm {δ : ℝ} {F : ℝ → ℝ} (h : 1 / 384 ≤ gammaEnergy δ F) :
    1 / 20 ≤ gammaNorm δ F := by
  unfold gammaNorm
  rw [show (1 : ℝ) / 20 = Real.sqrt (1 / 400) by
    rw [show (1 : ℝ) / 400 = (1 / 20) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- `‖v_3 + v_6‖_δ ≤ 2 C_1`. -/
theorem gammaNorm_centralProfile_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    gammaNorm δ centralProfile ≤ 2 * jetConst 1 := by
  have hδ : 0 < 5 + δ := by linarith
  unfold centralProfile
  refine (gammaNorm_add_le hδ (gammaFinite_jetProfile hδ (by norm_num))
    (gammaFinite_jetProfile hδ (by norm_num))).trans ?_
  have hC := jetConst_nonneg 1
  have b : ∀ y : ℝ, 1 ≤ y → gammaNorm δ (jetProfile y) ≤ jetConst 1 := by
    intro y hy
    refine (gammaNorm_jetProfile_le hδ0 hδ1 (by linarith)).trans ?_
    have : y ^ (-(1 + δ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
    nlinarith
  have := b 3 (by norm_num)
  have := b 6 (by norm_num)
  linarith

/-! ### Choosing the central scale -/

theorem gammaNorm_div_const {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ} (hF : GammaFinite δ F) {ε : ℝ}
    (hε : 0 < ε) : gammaNorm δ (fun t => F t / ε) = gammaNorm δ F / ε := by
  have e : (fun t => F t / ε) = fun t => ε⁻¹ * F t := by funext t; ring
  rw [e, gammaNorm_smul hδ hF, abs_inv, abs_of_pos hε]
  ring

/-- Two-sided control of `‖F‖` by a nearby `-G`. -/
theorem gammaNorm_near {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ} (hF : GammaFinite δ F)
    (hG : GammaFinite δ G) {e : ℝ} (h : gammaNorm δ (fun t => F t + G t) ≤ e) :
    gammaNorm δ G - e ≤ gammaNorm δ F ∧ gammaNorm δ F ≤ gammaNorm δ G + e := by
  have h1 := abs_gammaNorm_sub_le hδ hF hG.neg
  rw [gammaNorm_neg hδ hG] at h1
  have h2 : gammaNorm δ (fun t => F t - -G t) = gammaNorm δ (fun t => F t + G t) := by
    congr 1; funext t; ring
  rw [h2] at h1
  have := abs_le.mp (h1.trans h)
  constructor <;> linarith [this.1, this.2]

/-- Energy comparison to norm comparison. -/
theorem gammaNorm_le_of_gammaEnergy_le {δ : ℝ} (hδ : 0 < 5 + δ) {F G : ℝ → ℝ}
    (hF : GammaFinite δ F) (hG : GammaFinite δ G) {c : ℝ} (hc : 0 ≤ c)
    (h : gammaEnergy δ G ≤ c ^ 2 * gammaEnergy δ F) : gammaNorm δ G ≤ c * gammaNorm δ F := by
  have hG0 := gammaNorm_nonneg δ G
  have hF0 := gammaNorm_nonneg δ F
  rw [← gammaNorm_sq hδ hG, ← gammaNorm_sq hδ hF] at h
  have : gammaNorm δ G ^ 2 ≤ (c * gammaNorm δ F) ^ 2 := by rw [mul_pow]; exact h
  exact (pow_le_pow_iff_left₀ hG0 (by positivity) (by norm_num)).mp this

/-- The central packet: a uniform scale `ε` with all margins, for `0 ≤ δ ≤ δ₀`. -/
theorem exists_central_scale :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
      gammaNorm δ (insertTwo (centralPacket ε)) ≤ 888 / 1000 * gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (insertTwo (centralPacket ε)) ∧
      gammaNorm δ (centralPacket ε) ≤ (2 * jetConst 1 + 1) * ε ∧
      gammaNorm δ (fun t => insertTwo (centralPacket ε) t - 3 / 5 * ε * atom (3 / 2) t) ≤
        8163 / 10000 * gammaNorm δ (insertTwo (centralPacket ε)) := by
  obtain ⟨δa, hδa, ha⟩ := exists_dyadic_contraction_delta
  obtain ⟨δb, hδb, hb⟩ := exists_halfScale_compensation_delta
  set δ₀ := min (min δa δb) (1 / 2) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (lt_min hδa hδb) (by norm_num)
  have hC1 := jetConst_nonneg 1
  have hC2 := jetConst_nonneg 2
  set ε : ℝ := 1 / (2000000 * (jetConst 2 + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 4 := by
    rw [hε_def, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hC2ε : jetConst 2 * ε ≤ 1 / 2000000 := by
    rw [hε_def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨δ₀, hδ₀pos, min_le_right _ _, ε, hε, hε1, fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2.trans ((min_le_right _ _).trans (by norm_num))
  have hδa' : δ ∈ Set.Icc 0 δa := ⟨hδ0, hδ.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hδb' : δ ∈ Set.Icc 0 δb := ⟨hδ0, hδ.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hδ' : 0 < 5 + δ := by linarith
  have fB := gammaFinite_centralPacket hδ' hε.le
  have fV := gammaFinite_centralProfile hδ'
  have fDB := gammaFinite_insertTwo fB
  have fDV := gammaFinite_insertTwo fV
  -- approximations
  have aB := gammaNorm_centralPacket_approx hδ0 hδ1 hε (by linarith)
  have aD := gammaNorm_insertTwo_centralPacket_approx hδ0 hδ1 hε (by linarith)
  have nB := gammaNorm_near hδ' (fB.smul ε⁻¹ |>.congr (by funext t; ring)) fV aB
  have nD := gammaNorm_near hδ' (fDB.smul ε⁻¹ |>.congr (by funext t; ring)) fDV aD
  rw [gammaNorm_div_const hδ' fB hε] at nB
  rw [gammaNorm_div_const hδ' fDB hε] at nD
  -- the profile bounds
  have hV1 := one_div_twenty_le_gammaNorm (gammaEnergy_centralProfile_ge hδ0 hδ1)
  have hD1 := one_div_twenty_le_gammaNorm (gammaEnergy_insertTwo_centralProfile_ge hδ0 hδ1)
  have hVu := gammaNorm_centralProfile_le hδ0 hδ1
  have hratio : gammaNorm δ (insertTwo centralProfile) ≤ 8832 / 10000 * gammaNorm δ centralProfile := by
    refine gammaNorm_le_of_gammaEnergy_le hδ' fV fDV (by norm_num) ?_
    have h := ha δ hδa' 3 (by norm_num)
    rw [insertTwo_centralProfile]
    have e1 : (fun t => jetProfile 3 t - jetProfile (4 * 3) t) = fun t => jetProfile 3 t - jetProfile 12 t := by
      norm_num
    have e2 : (fun t => jetProfile 3 t + jetProfile (2 * 3) t) = centralProfile := by
      funext t; unfold centralProfile; norm_num
    rw [e1, e2] at h
    have hE := gammaEnergy_nonneg hδ' fV
    nlinarith
  -- the scaled norms
  have hBn : ε * (gammaNorm δ centralProfile - 4 * jetConst 2 * ε) ≤ gammaNorm δ (centralPacket ε) ∧
      gammaNorm δ (centralPacket ε) ≤ ε * (gammaNorm δ centralProfile + 4 * jetConst 2 * ε) := by
    constructor
    · have := nB.1; rw [le_div_iff₀ hε] at this; linarith
    · have := nB.2; rw [div_le_iff₀ hε] at this; linarith
  have hDn : ε * (gammaNorm δ (insertTwo centralProfile) - 8 * jetConst 2 * ε) ≤
      gammaNorm δ (insertTwo (centralPacket ε)) ∧
      gammaNorm δ (insertTwo (centralPacket ε)) ≤
        ε * (gammaNorm δ (insertTwo centralProfile) + 8 * jetConst 2 * ε) := by
    constructor
    · have := nD.1; rw [le_div_iff₀ hε] at this; linarith
    · have := nD.2; rw [div_le_iff₀ hε] at this; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the insertion ratio
    have key : gammaNorm δ (insertTwo centralProfile) + 8 * jetConst 2 * ε ≤
        888 / 1000 * (gammaNorm δ centralProfile - 4 * jetConst 2 * ε) := by linarith
    calc gammaNorm δ (insertTwo (centralPacket ε))
        ≤ ε * (gammaNorm δ (insertTwo centralProfile) + 8 * jetConst 2 * ε) := hDn.2
      _ ≤ ε * (888 / 1000 * (gammaNorm δ centralProfile - 4 * jetConst 2 * ε)) :=
          mul_le_mul_of_nonneg_left key hε.le
      _ = 888 / 1000 * (ε * (gammaNorm δ centralProfile - 4 * jetConst 2 * ε)) := by ring
      _ ≤ 888 / 1000 * gammaNorm δ (centralPacket ε) :=
          mul_le_mul_of_nonneg_left hBn.1 (by norm_num)
  · have := hBn.1
    have : ε / 40 ≤ ε * (gammaNorm δ centralProfile - 4 * jetConst 2 * ε) := by nlinarith
    linarith
  · have := hDn.1
    have : ε / 40 ≤ ε * (gammaNorm δ (insertTwo centralProfile) - 8 * jetConst 2 * ε) := by nlinarith
    linarith
  · have := hBn.2
    have : ε * (gammaNorm δ centralProfile + 4 * jetConst 2 * ε) ≤ (2 * jetConst 1 + 1) * ε := by
      nlinarith
    linarith
  · -- the half-scale compensation
    have fA := gammaFinite_atom hδ' (by norm_num : (0 : ℝ) < 3 / 2)
    set W : ℝ → ℝ := fun t => insertTwo centralProfile t + 3 / 5 * atom (3 / 2) t with hW
    have fW : GammaFinite δ W := fDV.add (fA.smul _)
    have hWr : gammaNorm δ W ≤ 8161 / 10000 * gammaNorm δ (insertTwo centralProfile) := by
      refine gammaNorm_le_of_gammaEnergy_le hδ' fDV fW (by norm_num) ?_
      have h := hb δ hδb' 3 (by norm_num)
      have e1 : dyadicJet 3 = insertTwo centralProfile := by
        rw [insertTwo_centralProfile]; funext t; unfold dyadicJet; norm_num
      rw [e1, show (3 : ℝ) / 2 = 3 / 2 from rfl] at h
      have hE := gammaEnergy_nonneg hδ' fDV
      have e2 : W = fun t => insertTwo centralProfile t + 3 / 5 * atom (3 / 2) t := rfl
      rw [e2]
      nlinarith
    set Cε : ℝ → ℝ := fun t => insertTwo (centralPacket ε) t - 3 / 5 * ε * atom (3 / 2) t with hCε
    have fC : GammaFinite δ Cε := fDB.sub (fA.smul _)
    have aC : gammaNorm δ (fun t => Cε t / ε + W t) ≤ 8 * jetConst 2 * ε := by
      have e : (fun t => Cε t / ε + W t) =
          fun t => insertTwo (centralPacket ε) t / ε + insertTwo centralProfile t := by
        funext t; simp only [hCε, hW]; field_simp; ring
      rw [e]; exact aD
    have nC := gammaNorm_near hδ' (fC.smul ε⁻¹ |>.congr (by funext t; ring)) fW aC
    rw [gammaNorm_div_const hδ' fC hε] at nC
    have hCu : gammaNorm δ Cε ≤ ε * (gammaNorm δ W + 8 * jetConst 2 * ε) := by
      have := nC.2; rw [div_le_iff₀ hε] at this; linarith
    have key : gammaNorm δ W + 8 * jetConst 2 * ε ≤
        8163 / 10000 * (gammaNorm δ (insertTwo centralProfile) - 8 * jetConst 2 * ε) := by
      linarith
    calc gammaNorm δ Cε ≤ ε * (gammaNorm δ W + 8 * jetConst 2 * ε) := hCu
      _ ≤ ε * (8163 / 10000 * (gammaNorm δ (insertTwo centralProfile) - 8 * jetConst 2 * ε)) :=
          mul_le_mul_of_nonneg_left key hε.le
      _ = 8163 / 10000 * (ε * (gammaNorm δ (insertTwo centralProfile) - 8 * jetConst 2 * ε)) := by
          ring
      _ ≤ 8163 / 10000 * gammaNorm δ (insertTwo (centralPacket ε)) :=
          mul_le_mul_of_nonneg_left hDn.1 (by norm_num)

/-! ### Narrow bands -/

/-- `‖f_b - f_a‖_δ ≤ 4 C_1 η R^(-(1+δ)/2)` for `R ≤ a ≤ b ≤ (1+η) a`, `η ≤ 1`. -/
theorem gammaNorm_atom_band {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {R a b η : ℝ} (hR : 0 < R)
    (hRa : R ≤ a) (hab : a ≤ b) (hb : b ≤ (1 + η) * a) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    gammaNorm δ (fun t => atom b t - atom a t) ≤ 4 * jetConst 1 * η * R ^ (-(1 + δ) / 2) := by
  have ha : 0 < a := hR.trans_le hRa
  have hC := jetConst_nonneg 1
  refine (gammaNorm_atom_sub_le hδ0 hδ1 ha hab).trans ?_
  have e : a ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ = a ^ (-(1 + δ) / 2) := by
    rw [← Real.rpow_neg ha.le, ← Real.rpow_two, ← Real.rpow_add ha]; ring_nf
  have hb2 : b ^ 2 ≤ 4 * a ^ 2 := by
    have h2a : b ≤ 2 * a := by nlinarith
    have hb0 : 0 ≤ b := by linarith
    nlinarith
  have hp : 0 ≤ (a ^ ((5 + δ) / 2))⁻¹ := by positivity
  have hRa' : a ^ (-(1 + δ) / 2) ≤ R ^ (-(1 + δ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hR hRa (by linarith)
  calc (b - a) * (jetConst 1 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a)
      ≤ (η * a) * (jetConst 1 * (4 * a ^ 2) * (a ^ ((5 + δ) / 2))⁻¹ / a) := by
        apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
        gcongr
    _ = 4 * jetConst 1 * η * (a ^ 2 * (a ^ ((5 + δ) / 2))⁻¹) := by field_simp
    _ = 4 * jetConst 1 * η * a ^ (-(1 + δ) / 2) := by rw [e]
    _ ≤ 4 * jetConst 1 * η * R ^ (-(1 + δ) / 2) := by gcongr

/-- A literal tuple in the four bands is within `16 C_1 η R^(-(1+δ)/2)` of the dilated central
packet. -/
theorem gammaNorm_tuple_sub_central {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {R ε η : ℝ} (hR : 0 < R)
    (hε : 0 ≤ ε) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {r r' p p' : ℝ}
    (hr : R < r) (hr' : r ≤ (1 + η) * R) (hs : 2 * R < r') (hs' : r' ≤ (1 + η) * (2 * R))
    (hp : 3 * (1 + ε) * R < p) (hp' : p ≤ (1 + η) * (3 * (1 + ε) * R))
    (hq : 6 * (1 + ε) * R < p') (hq' : p' ≤ (1 + η) * (6 * (1 + ε) * R)) :
    gammaNorm δ (fun t => twoDipolePrecursor (3 * r) p (3 * r') p' t -
      dilate R (centralPacket ε) t) ≤ 16 * jetConst 1 * η * R ^ (-(1 + δ) / 2) := by
  have hδ : 0 < 5 + δ := by linarith
  have hsc : dilate R (centralPacket ε) =
      twoDipolePrecursor (R * 3) (R * (3 * (1 + ε))) (R * 6) (R * (6 * (1 + ε))) := by
    unfold centralPacket; rw [twoDipolePrecursor_scale]
  rw [hsc]
  have f : ∀ x : ℝ, 0 < x → GammaFinite δ (atom x) := fun x hx => gammaFinite_atom hδ hx
  have e : (fun t => twoDipolePrecursor (3 * r) p (3 * r') p' t -
      twoDipolePrecursor (R * 3) (R * (3 * (1 + ε))) (R * 6) (R * (6 * (1 + ε))) t) =
      fun t => ((atom (3 * r) t - atom (R * 3) t) + (-1) * (atom p t - atom (R * (3 * (1 + ε))) t)) +
        ((atom (3 * r') t - atom (R * 6) t) + (-1) * (atom p' t - atom (R * (6 * (1 + ε))) t)) := by
    funext t; unfold twoDipolePrecursor; ring
  rw [e]
  have hR3 : 0 < R * 3 := by positivity
  have hRe3 : 0 < R * (3 * (1 + ε)) := by positivity
  have hR6 : 0 < R * 6 := by positivity
  have hRe6 : 0 < R * (6 * (1 + ε)) := by positivity
  have d1 : GammaFinite δ (fun t => atom (3 * r) t - atom (R * 3) t) :=
    (f _ (by linarith)).sub (f _ hR3)
  have d2 : GammaFinite δ (fun t => atom p t - atom (R * (3 * (1 + ε))) t) :=
    (f _ (by nlinarith)).sub (f _ hRe3)
  have d3 : GammaFinite δ (fun t => atom (3 * r') t - atom (R * 6) t) :=
    (f _ (by linarith)).sub (f _ hR6)
  have d4 : GammaFinite δ (fun t => atom p' t - atom (R * (6 * (1 + ε))) t) :=
    (f _ (by nlinarith)).sub (f _ hRe6)
  refine (gammaNorm_add_le hδ (d1.add (d2.smul _)) (d3.add (d4.smul _))).trans ?_
  refine (add_le_add (gammaNorm_add_le hδ d1 (d2.smul _)) (gammaNorm_add_le hδ d3 (d4.smul _))).trans ?_
  rw [gammaNorm_smul hδ d2, gammaNorm_smul hδ d4, abs_neg, abs_one, one_mul, one_mul]
  have b1 := gammaNorm_atom_band hδ0 hδ1 hR (a := R * 3) (b := 3 * r) (η := η) (by linarith)
    (by linarith) (by nlinarith) hη0 hη1
  have b2 := gammaNorm_atom_band hδ0 hδ1 hR (a := R * (3 * (1 + ε))) (b := p) (η := η)
    (by nlinarith) (by nlinarith) (by nlinarith) hη0 hη1
  have b3 := gammaNorm_atom_band hδ0 hδ1 hR (a := R * 6) (b := 3 * r') (η := η) (by linarith)
    (by linarith) (by nlinarith) hη0 hη1
  have b4 := gammaNorm_atom_band hδ0 hδ1 hR (a := R * (6 * (1 + ε))) (b := p') (η := η)
    (by nlinarith) (by nlinarith) (by nlinarith) hη0 hη1
  linarith

/-! ### Prime supply in fixed relative bands -/

open GaloisForLFunctions.HTGeometry in
/-- **Fixed-relative-interval prime supply.**  For `0 < α < β`, eventually in `R` the band
`(αR, βR]` holds at least `(β-α)/4 · R/log R` primes. -/
theorem eventually_card_primes_band {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∀ᶠ R : ℝ in atTop, (β - α) / 4 * (R / Real.log R) ≤
      ((primesInIoc ⌊α * R⌋₊ ⌊β * R⌋₊).card : ℝ) := by
  have hK : 1 < β / α := by rw [one_lt_div hα]; exact hαβ
  have hw := eventually_primeCount_window_ge hK
  have hlin : Tendsto (fun R : ℝ => α * R) atTop atTop := tendsto_id.const_mul_atTop hα
  have hw' := hlin.eventually hw
  filter_upwards [hw', eventually_ge_atTop (max (max 2 (1 / α + 1)) α)] with R hR hR2
  have hR1 : 2 ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR2)
  have hRα : α ≤ R := (le_max_right _ _).trans hR2
  have hαR1 : 1 < α * R := by
    have h := (le_max_right _ _).trans ((le_max_left _ _).trans hR2)
    have : 1 / α < R := by linarith
    rw [div_lt_iff₀ hα] at this; linarith
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogαR : 0 < Real.log (α * R) := Real.log_pos hαR1
  have hlog2 : Real.log (α * R) ≤ 2 * Real.log R := by
    rw [← Real.log_rpow (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hKx : β / α * (α * R) = β * R := by field_simp
  rw [hKx] at hR
  have hfloor : ⌊α * R⌋₊ ≤ ⌊β * R⌋₊ := Nat.floor_le_floor (by nlinarith)
  rw [card_primesInIoc hfloor]
  refine le_trans ?_ hR
  have e : (β / α - 1) / 2 * (α * R / Real.log (α * R)) = (β - α) / 2 * (R / Real.log (α * R)) := by
    field_simp
  rw [e]
  have hβα : 0 ≤ β - α := by linarith
  have : R / Real.log R / 2 ≤ R / Real.log (α * R) := by
    rw [div_div, div_le_div_iff₀ (by positivity) hlogαR]; nlinarith
  nlinarith

open GaloisForLFunctions.HTGeometry in
theorem mem_primesInIoc_band {α β R : ℝ} (hβR : 0 ≤ β * R) {p : ℕ}
    (hp : p ∈ primesInIoc ⌊α * R⌋₊ ⌊β * R⌋₊) : p.Prime ∧ α * R < p ∧ (p : ℝ) ≤ β * R := by
  obtain ⟨hpr, h1, h2⟩ := mem_primesInIoc hp
  exact ⟨hpr, Nat.lt_of_floor_lt h1, (Nat.le_floor_iff hβR).mp h2⟩

/-! ### Sums of aligned tuples -/

/-- The macroscopic precursor `P = Σ_i (f_(3r_i) - f_(p_i) + f_(3r'_i) - f_(p'_i))`. -/
def tuplePacket {M : ℕ} (r r' p p' : Fin M → ℕ) (t : ℝ) : ℝ :=
  ∑ i, twoDipolePrecursor (3 * (r i : ℝ)) (p i) (3 * (r' i : ℝ)) (p' i) t

/-- Band membership of one tuple at scale `R`, relative widths `ε, η`. -/
def InBands (R ε η : ℝ) (r r' p p' : ℕ) : Prop :=
  R < r ∧ (r : ℝ) ≤ (1 + η) * R ∧ 2 * R < r' ∧ (r' : ℝ) ≤ (1 + η) * (2 * R) ∧
    3 * (1 + ε) * R < p ∧ (p : ℝ) ≤ (1 + η) * (3 * (1 + ε) * R) ∧
    6 * (1 + ε) * R < p' ∧ (p' : ℝ) ≤ (1 + η) * (6 * (1 + ε) * R)

theorem gammaFinite_tuplePacket {δ : ℝ} (hδ : 0 < 5 + δ) {R : ℝ} (hR : 0 < R) {ε η : ℝ}
    (hε : 0 ≤ ε) {M : ℕ} {r r' p p' : Fin M → ℕ}
    (hb : ∀ i, InBands R ε η (r i) (r' i) (p i) (p' i)) : GammaFinite δ (tuplePacket r r' p p') := by
  unfold tuplePacket
  refine GammaFinite.sum _ fun i _ => ?_
  obtain ⟨h1, -, h3, -, h5, -, h7, -⟩ := hb i
  exact gammaFinite_twoDipolePrecursor hδ (by linarith) (by nlinarith) (by linarith) (by nlinarith)

/-- `D_2` and dilation of the central packet. -/
theorem insertTwo_dilate_centralPacket (R ε : ℝ) :
    insertTwo (dilate R (centralPacket ε)) = dilate R (insertTwo (centralPacket ε)) :=
  insertTwo_dilate R _

/-- The linear insertion of a finite sum. -/
theorem insertTwo_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ) :
    insertTwo (fun t => ∑ i ∈ s, F i t) = fun t => ∑ i ∈ s, insertTwo (F i) t := by
  funext t
  unfold insertTwo dilate
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]

private theorem sq_le_gammaEnergy_of_le {δ : ℝ} (hδ : 0 < 5 + δ) {x : ℝ} (hx : 0 ≤ x)
    {F : ℝ → ℝ} (hF : GammaFinite δ F) (h : x ≤ gammaNorm δ F) : x ^ 2 ≤ gammaEnergy δ F := by
  rw [← gammaNorm_sq hδ hF]
  exact pow_le_pow_left₀ hx h 2

/-- **Aligned tuple sums.**  Given the central margins on `[0, δ₀]`, any nonempty sum of tuples
in the bands with `16 C_1 η ≤ ε/(40000(2C_1+1))` satisfies the macroscopic bounds. -/
theorem tuplePacket_bounds {δ₀ ε η : ℝ} (hδ₀1 : δ₀ ≤ 1 / 2) (hε : 0 < ε)
    (hcentral : ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
      gammaNorm δ (insertTwo (centralPacket ε)) ≤ 888 / 1000 * gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (insertTwo (centralPacket ε)) ∧
      gammaNorm δ (centralPacket ε) ≤ (2 * jetConst 1 + 1) * ε)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hηε : 16 * jetConst 1 * η ≤ ε / (40000 * (2 * jetConst 1 + 1)))
    {R : ℝ} (hR : 0 < R) {M : ℕ} (hM : 1 ≤ M) {r r' p p' : Fin M → ℕ}
    (hb : ∀ i, InBands R ε η (r i) (r' i) (p i) (p' i)) :
    ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
      gammaEnergy δ (insertTwo (tuplePacket r r' p p')) <
        4 / 5 * gammaEnergy δ (tuplePacket r r' p p') ∧
      (ε / 50) ^ 2 * (M : ℝ) ^ 2 * R ^ (-1 - δ) ≤ gammaEnergy δ (tuplePacket r r' p p') ∧
      (ε / 50) ^ 2 * (M : ℝ) ^ 2 * R ^ (-1 - δ) ≤
        gammaEnergy δ (insertTwo (tuplePacket r r' p p')) := by
  intro δ hδ
  obtain ⟨hD, hBl, hDl, hBu⟩ := hcentral δ hδ
  have hδ0 := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2.trans (hδ₀1.trans (by norm_num))
  have hδ' : 0 < 5 + δ := by linarith
  have hC1 := jetConst_nonneg 1
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  -- the scale factor and the dilated central packet
  have hρ0 : 0 < R ^ (-(1 + δ) / 2) := Real.rpow_pos_of_pos hR _
  have fBε := gammaFinite_centralPacket hδ' hε.le
  have fB : GammaFinite δ (dilate R (centralPacket ε)) := fBε.dilate hR
  have fDB : GammaFinite δ (insertTwo (dilate R (centralPacket ε))) := gammaFinite_insertTwo fB
  have nB : gammaNorm δ (dilate R (centralPacket ε)) =
      R ^ (-(1 + δ) / 2) * gammaNorm δ (centralPacket ε) := gammaNorm_dilate hR _
  have nDB : gammaNorm δ (insertTwo (dilate R (centralPacket ε))) =
      R ^ (-(1 + δ) / 2) * gammaNorm δ (insertTwo (centralPacket ε)) := by
    rw [insertTwo_dilate_centralPacket, gammaNorm_dilate hR]
  have fP := gammaFinite_tuplePacket hδ' hR hε.le hb
  have fU : GammaFinite δ (fun t => (M : ℝ) * dilate R (centralPacket ε) t) := fB.smul _
  -- tuple errors: `‖T_i - B‖ ≤ τ gammaNorm δ (dilate R (centralPacket ε))` with `τ = 1/(1000(2C_1+1))`
  have hTi : ∀ i, gammaNorm δ (fun t => twoDipolePrecursor (3 * (r i : ℝ)) (p i)
      (3 * (r' i : ℝ)) (p' i) t - dilate R (centralPacket ε) t) ≤
      gammaNorm δ (dilate R (centralPacket ε)) / (1000 * (2 * jetConst 1 + 1)) := by
    intro i
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb i
    refine (gammaNorm_tuple_sub_central hδ0 hδ1 hR hε.le hη0 hη1 h1 h2 h3 h4 h5 h6 h7 h8).trans ?_
    rw [nB]
    have h40 : 16 * jetConst 1 * η ≤ (ε / 40) / (1000 * (2 * jetConst 1 + 1)) := by
      calc 16 * jetConst 1 * η ≤ ε / (40000 * (2 * jetConst 1 + 1)) := hηε
        _ = (ε / 40) / (1000 * (2 * jetConst 1 + 1)) := by field_simp; ring
    have h41 : (ε / 40) / (1000 * (2 * jetConst 1 + 1)) ≤
        gammaNorm δ (centralPacket ε) / (1000 * (2 * jetConst 1 + 1)) :=
      div_le_div_of_nonneg_right hBl (by positivity)
    calc 16 * jetConst 1 * η * R ^ (-(1 + δ) / 2) ≤ gammaNorm δ (centralPacket ε) / (1000 * (2 * jetConst 1 + 1)) * R ^ (-(1 + δ) / 2) :=
          mul_le_mul_of_nonneg_right (h40.trans h41) hρ0.le
      _ = R ^ (-(1 + δ) / 2) * gammaNorm δ (centralPacket ε) / (1000 * (2 * jetConst 1 + 1)) := by ring
  have fTi : ∀ i : Fin M, GammaFinite δ (fun t => twoDipolePrecursor (3 * (r i : ℝ)) (p i)
      (3 * (r' i : ℝ)) (p' i) t - dilate R (centralPacket ε) t) := by
    intro i
    obtain ⟨h1, -, h3, -, h5, -, h7, -⟩ := hb i
    exact (gammaFinite_twoDipolePrecursor hδ' (by linarith) (by nlinarith) (by linarith)
      (by nlinarith)).sub fB
  set E : ℝ := (M : ℝ) * (gammaNorm δ (dilate R (centralPacket ε)) / (1000 * (2 * jetConst 1 + 1))) with hE
  have hPU : gammaNorm δ (fun t => tuplePacket r r' p p' t + -((M : ℝ) * dilate R (centralPacket ε) t))
      ≤ E := by
    have e : (fun t => tuplePacket r r' p p' t + -((M : ℝ) * dilate R (centralPacket ε) t)) =
        fun t => ∑ i : Fin M, (twoDipolePrecursor (3 * (r i : ℝ)) (p i) (3 * (r' i : ℝ)) (p' i) t -
          dilate R (centralPacket ε) t) := by
      funext t
      simp only [tuplePacket, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [e]
    refine (gammaNorm_sum_le hδ' _ fun i _ => fTi i).trans ?_
    calc ∑ i : Fin M, gammaNorm δ (fun t => twoDipolePrecursor (3 * (r i : ℝ)) (p i)
          (3 * (r' i : ℝ)) (p' i) t - dilate R (centralPacket ε) t)
        ≤ ∑ _i : Fin M, gammaNorm δ (dilate R (centralPacket ε)) / (1000 * (2 * jetConst 1 + 1)) := Finset.sum_le_sum fun i _ => hTi i
      _ = E := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hDPU : gammaNorm δ (fun t => insertTwo (tuplePacket r r' p p') t +
      -insertTwo (fun t => (M : ℝ) * dilate R (centralPacket ε) t) t) ≤ 2 * E := by
    have e : (fun t => insertTwo (tuplePacket r r' p p') t +
        -insertTwo (fun t => (M : ℝ) * dilate R (centralPacket ε) t) t) =
        insertTwo (fun t => tuplePacket r r' p p' t + -((M : ℝ) * dilate R (centralPacket ε) t)) := by
      funext t; unfold insertTwo dilate; ring
    rw [e]
    exact (gammaNorm_insertTwo_le hδ0 (fP.add fU.neg)).trans (by linarith)
  have nU : gammaNorm δ (fun t => (M : ℝ) * dilate R (centralPacket ε) t) = (M : ℝ) * gammaNorm δ (dilate R (centralPacket ε)) := by
    rw [gammaNorm_smul hδ' fB, abs_of_pos (by linarith)]
  have nDU : gammaNorm δ (insertTwo (fun t => (M : ℝ) * dilate R (centralPacket ε) t)) =
      (M : ℝ) * gammaNorm δ (insertTwo (dilate R (centralPacket ε))) := by
    have e : insertTwo (fun t => (M : ℝ) * dilate R (centralPacket ε) t) =
        fun t => (M : ℝ) * insertTwo (dilate R (centralPacket ε)) t := by
      funext t; unfold insertTwo dilate; ring
    rw [e, gammaNorm_smul hδ' fDB, abs_of_pos (by linarith)]
  have fDP := gammaFinite_insertTwo fP
  have fDU := gammaFinite_insertTwo fU
  have nP := gammaNorm_near (e := E) hδ' fP fU.neg hPU
  rw [gammaNorm_neg hδ' fU, nU] at nP
  have nDP := gammaNorm_near (e := 2 * E) hδ' fDP fDU.neg hDPU
  rw [gammaNorm_neg hδ' fDU, nDU] at nDP
  -- scalar bookkeeping with the single atom `X = M gammaNorm δ (dilate R (centralPacket ε))`
  set X := (M : ℝ) * gammaNorm δ (dilate R (centralPacket ε)) with hX
  have hb0 : 0 ≤ gammaNorm δ (dilate R (centralPacket ε)) := gammaNorm_nonneg _ _
  have hEX : E ≤ X / 1000 := by
    rw [hE, hX]
    have hd : (1 : ℝ) ≤ 2 * jetConst 1 + 1 := by linarith
    have : gammaNorm δ (dilate R (centralPacket ε)) / (1000 * (2 * jetConst 1 + 1)) ≤ gammaNorm δ (dilate R (centralPacket ε)) / 1000 :=
      div_le_div_of_nonneg_left hb0 (by norm_num) (by nlinarith)
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ M)
    linarith
  have hEρ : E ≤ (M : ℝ) * (R ^ (-(1 + δ) / 2) * ε / 1000) := by
    rw [hE]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [div_le_iff₀ (by positivity), nB]
    calc R ^ (-(1 + δ) / 2) * gammaNorm δ (centralPacket ε) ≤ R ^ (-(1 + δ) / 2) * ((2 * jetConst 1 + 1) * ε) := by gcongr
      _ = R ^ (-(1 + δ) / 2) * ε / 1000 * (1000 * (2 * jetConst 1 + 1)) := by ring
  have hDB : gammaNorm δ (insertTwo (dilate R (centralPacket ε))) ≤ 888 / 1000 * gammaNorm δ (dilate R (centralPacket ε)) := by
    rw [nDB, nB]
    calc R ^ (-(1 + δ) / 2) * gammaNorm δ (insertTwo (centralPacket ε)) ≤ R ^ (-(1 + δ) / 2) * (888 / 1000 * gammaNorm δ (centralPacket ε)) :=
          mul_le_mul_of_nonneg_left hD hρ0.le
      _ = 888 / 1000 * (R ^ (-(1 + δ) / 2) * gammaNorm δ (centralPacket ε)) := by ring
  have hDBl : R ^ (-(1 + δ) / 2) * (ε / 40) ≤ gammaNorm δ (insertTwo (dilate R (centralPacket ε))) := by
    rw [nDB]; exact mul_le_mul_of_nonneg_left hDl hρ0.le
  have hBlow : R ^ (-(1 + δ) / 2) * (ε / 40) ≤ gammaNorm δ (dilate R (centralPacket ε)) := by
    rw [nB]; exact mul_le_mul_of_nonneg_left hBl hρ0.le
  have hMD : (M : ℝ) * gammaNorm δ (insertTwo (dilate R (centralPacket ε))) ≤ 888 / 1000 * X := by
    rw [hX]; have := mul_le_mul_of_nonneg_left hDB (by linarith : (0 : ℝ) ≤ M); linarith
  have hPl : 999 / 1000 * X ≤ gammaNorm δ (tuplePacket r r' p p') := by linarith [nP.1]
  have hDPu : gammaNorm δ (insertTwo (tuplePacket r r' p p')) ≤ 890 / 1000 * X := by
    linarith [nDP.2]
  have hMρ : (M : ℝ) * (R ^ (-(1 + δ) / 2) * (ε / 40)) ≤ X := by
    rw [hX]; exact mul_le_mul_of_nonneg_left hBlow (by linarith)
  have hMρD : (M : ℝ) * (R ^ (-(1 + δ) / 2) * (ε / 40)) ≤
      (M : ℝ) * gammaNorm δ (insertTwo (dilate R (centralPacket ε))) :=
    mul_le_mul_of_nonneg_left hDBl (by linarith)
  have hDPl : (M : ℝ) * (R ^ (-(1 + δ) / 2) * (ε / 50)) ≤ gammaNorm δ (insertTwo (tuplePacket r r' p p')) := by
    have h1 := nDP.1
    have h2 : (M : ℝ) * (R ^ (-(1 + δ) / 2) * (ε / 50)) + 2 * ((M : ℝ) * (R ^ (-(1 + δ) / 2) * ε / 1000)) ≤
        (M : ℝ) * (R ^ (-(1 + δ) / 2) * (ε / 40)) := by
      have : 0 ≤ (M : ℝ) * (R ^ (-(1 + δ) / 2) * ε) := by positivity
      linarith
    linarith
  have hPl2 : (M : ℝ) * (R ^ (-(1 + δ) / 2) * (ε / 50)) ≤ gammaNorm δ (tuplePacket r r' p p') := by
    have : 0 ≤ (M : ℝ) * (R ^ (-(1 + δ) / 2) * ε) := by positivity
    linarith
  have hsq : ((M : ℝ) * (R ^ (-(1 + δ) / 2) * (ε / 50))) ^ 2 = (ε / 50) ^ 2 * (M : ℝ) ^ 2 * R ^ (-1 - δ) := by
    have hρ2 : (R ^ (-(1 + δ) / 2)) ^ 2 = R ^ (-1 - δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]; norm_num; ring_nf
    rw [mul_pow, mul_pow, hρ2]; ring
  refine ⟨?_, ?_, ?_⟩
  · have hXpos : 0 < X := by
      have : 0 < (M : ℝ) * (R ^ (-(1 + δ) / 2) * (ε / 40)) := by positivity
      linarith
    have hr : gammaNorm δ (insertTwo (tuplePacket r r' p p')) ≤
        891 / 1000 * gammaNorm δ (tuplePacket r r' p p') := by linarith
    rw [← gammaNorm_sq hδ' fDP, ← gammaNorm_sq hδ' fP]
    have h0 := gammaNorm_nonneg δ (insertTwo (tuplePacket r r' p p'))
    have h1 := pow_le_pow_left₀ h0 hr 2
    have hPpos : 0 < gammaNorm δ (tuplePacket r r' p p') := by linarith
    have hp2 : 0 < gammaNorm δ (tuplePacket r r' p p') ^ 2 := by positivity
    have : (891 / 1000 * gammaNorm δ (tuplePacket r r' p p')) ^ 2 <
        4 / 5 * gammaNorm δ (tuplePacket r r' p p') ^ 2 := by
      rw [mul_pow]; exact mul_lt_mul_of_pos_right (by norm_num) hp2
    linarith
  · rw [← hsq]; exact sq_le_gammaEnergy_of_le hδ' (by positivity) fP hPl2
  · rw [← hsq]; exact sq_le_gammaEnergy_of_le hδ' (by positivity) fDP hDPl

/-! ### The eight literal atoms of an inserted tuple -/

/-- The eight atoms `3r, 6r, p, 2p, 3r', 6r', p', 2p'` of the `2`-inserted tuple. -/
def eightAtom (r r' p p' : ℕ) (k : Fin 8) : ℕ := ![3 * r, 6 * r, p, 2 * p, 3 * r', 6 * r', p', 2 * p'] k

/-- Their coefficients in `D_2 (f_(3r) - f_p + f_(3r') - f_(p'))`. -/
def eightSign (k : Fin 8) : ℤ := ![1, -1, -1, 1, 1, -1, -1, 1] k

theorem insertTwo_tuple_eq_eight (r r' p p' : ℕ) (t : ℝ) :
    insertTwo (twoDipolePrecursor (3 * (r : ℝ)) p (3 * (r' : ℝ)) p') t =
      ∑ k, (eightSign k : ℝ) * atom (eightAtom r r' p p' k) t := by
  rw [insertTwo_twoDipolePrecursor, Fin.sum_univ_eight]
  simp [eightSign, eightAtom]
  ring_nf

/-- The coefficients are the literal Möbius values. -/
theorem moebius_eightAtom {r r' p p' : ℕ} (hr : r.Prime) (hr' : r'.Prime) (hp : p.Prime)
    (hp' : p'.Prime) (h6 : 6 < r) (h6' : 6 < r') (h2 : 2 < p) (h2' : 2 < p') (k : Fin 8) :
    μ (eightAtom r r' p p' k) = eightSign k := by
  fin_cases k <;> simp only [eightAtom, eightSign] <;>
  first
  | exact moebius_three_mul hr (by omega)
  | exact moebius_six_mul hr h6
  | exact moebius_prime _ hp
  | exact moebius_two_mul hp h2
  | exact moebius_three_mul hr' (by omega)
  | exact moebius_six_mul hr' h6'
  | exact moebius_prime _ hp'
  | exact moebius_two_mul hp' h2'

/-- The value class of each atom slot. -/
def eightClass (k : Fin 8) : ℕ := ![0, 2, 1, 3, 2, 4, 3, 5] k

/-- Lower/upper band ends of each value class, in units of `R`. -/
def classLo (ε : ℝ) : ℕ → ℝ
  | 0 => 3
  | 1 => 3 * (1 + ε)
  | 2 => 6
  | 3 => 6 * (1 + ε)
  | 4 => 12
  | _ => 12 * (1 + ε)

theorem eightAtom_mem_class {R ε η : ℝ} {r r' p p' : ℕ}
    (hb : InBands R ε η r r' p p') (k : Fin 8) :
    classLo ε (eightClass k) * R < eightAtom r r' p p' k ∧
      (eightAtom r r' p p' k : ℝ) ≤ (1 + η) * (classLo ε (eightClass k) * R) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
  fin_cases k <;> simp only [eightAtom, eightClass, classLo] <;>
    push_cast <;> norm_num <;> constructor <;> nlinarith

/-- **The eight atoms are distinct across all tuples.** -/
theorem eightAtom_injective {R ε η : ℝ} (hR : 0 < R) (hη0 : 0 ≤ η) (hηε : η ≤ ε) (hε : ε ≤ 1 / 4)
    {M : ℕ} {r r' p p' : Fin M → ℕ} (hr : Function.Injective r) (hr' : Function.Injective r')
    (hp : Function.Injective p) (hp' : Function.Injective p')
    (hprime : ∀ i, (r' i).Prime ∧ (p' i).Prime ∧ 2 < r' i ∧ 2 < p' i)
    (hb : ∀ i, InBands R ε η (r i) (r' i) (p i) (p' i)) :
    Function.Injective (fun ik : Fin M × Fin 8 => eightAtom (r ik.1) (r' ik.1) (p ik.1) (p' ik.1) ik.2) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  simp only at h
  -- classes agree
  have hcl : eightClass k = eightClass l := by
    by_contra hne
    have hk := eightAtom_mem_class (hb i) k
    have hl := eightAtom_mem_class (hb j) l
    have hsep : ∀ c d : ℕ, c < d → d < 6 → (1 + η) * (classLo ε c * R) ≤ classLo ε d * R := by
      intro c d hcd hd
      have hε0 : 0 ≤ ε := hη0.trans hηε
      have hmono : ∀ c : ℕ, c < 5 → (1 + η) * classLo ε c ≤ classLo ε (c + 1) := by
        intro c hc
        interval_cases c <;> simp [classLo] <;> nlinarith
      have hpos : ∀ c : ℕ, c < 6 → 0 ≤ classLo ε c := by
        intro c hc; interval_cases c <;> simp [classLo] <;> nlinarith
      have hstep : ∀ c : ℕ, c < 5 → classLo ε c ≤ classLo ε (c + 1) := by
        intro c hc
        have := hmono c hc
        have := hpos c (by omega)
        nlinarith
      have hchain : ∀ n : ℕ, c + 1 + n < 6 → classLo ε (c + 1) ≤ classLo ε (c + 1 + n) := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ n ih =>
            intro hn
            have := ih (by omega)
            have := hstep (c + 1 + n) (by omega)
            rw [show c + 1 + (n + 1) = c + 1 + n + 1 by ring]
            linarith
      have h1 := hmono c (by omega)
      have h2 := hchain (d - (c + 1)) (by omega)
      rw [show c + 1 + (d - (c + 1)) = d by omega] at h2
      nlinarith
    have hk6 : eightClass k < 6 := by fin_cases k <;> simp [eightClass]
    have hl6 : eightClass l < 6 := by fin_cases l <;> simp [eightClass]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hsep _ _ hlt hl6
      have : (eightAtom (r i) (r' i) (p i) (p' i) k : ℝ) < eightAtom (r j) (r' j) (p j) (p' j) l := by
        linarith [hk.2, hl.1]
      rw [h] at this; exact lt_irrefl _ this
    · have := hsep _ _ hlt hk6
      have : (eightAtom (r j) (r' j) (p j) (p' j) l : ℝ) < eightAtom (r i) (r' i) (p i) (p' i) k := by
        linarith [hk.1, hl.2]
      rw [h] at this; exact lt_irrefl _ this
  -- within a class: same slot, or opposite parity
  obtain ⟨hri, hpi, hr2, hp2⟩ := hprime i
  obtain ⟨hrj, hpj, hr2j, hp2j⟩ := hprime j
  have oddr : ∀ m, (r' m).Prime → 2 < r' m → r' m % 2 = 1 := fun m hm h2 =>
    (hm.eq_two_or_odd).resolve_left (by omega)
  have oddp : ∀ m, (p' m).Prime → 2 < p' m → p' m % 2 = 1 := fun m hm h2 =>
    (hm.eq_two_or_odd).resolve_left (by omega)
  have o1 := oddr i hri hr2
  have o2 := oddr j hrj hr2j
  have o3 := oddp i hpi hp2
  have o4 := oddp j hpj hp2j
  fin_cases k <;> fin_cases l <;> simp [eightClass, eightAtom] at hcl h ⊢ <;>
    first
    | omega
    | (have := hr (by omega); simp_all)
    | (have := hr' (by omega); simp_all)
    | (have := hp (by omega); simp_all)
    | (have := hp' (by omega); simp_all)

/-! ### Selecting the macroscopic packet -/

open GaloisForLFunctions.HTGeometry in
/-- `M` distinct primes from a band, enumerated increasingly. -/
theorem exists_band_enumeration {α β R : ℝ} (hβR : 0 ≤ β * R) {M : ℕ}
    (hM : M ≤ (primesInIoc ⌊α * R⌋₊ ⌊β * R⌋₊).card) :
    ∃ e : Fin M → ℕ, StrictMono e ∧ ∀ i, (e i).Prime ∧ α * R < e i ∧ (e i : ℝ) ≤ β * R := by
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq hM
  refine ⟨T.orderEmbOfFin hTc, (T.orderEmbOfFin hTc).strictMono, fun i => ?_⟩
  exact mem_primesInIoc_band hβR (hTS (T.orderEmbOfFin_mem hTc i))

/-- The macroscopic parameters: `δ₀`, the central scale `ε` with its margins, and a band width `η`
with `16 C_1 η ≤ ε/(40000(2C_1+1))`. -/
theorem exists_macroscopic_parameters :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      16 * jetConst 1 * η ≤ ε / (400000000 * (2 * jetConst 1 + 1)) ∧
      ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
        gammaNorm δ (insertTwo (centralPacket ε)) ≤ 888 / 1000 * gammaNorm δ (centralPacket ε) ∧
        ε / 40 ≤ gammaNorm δ (centralPacket ε) ∧
        ε / 40 ≤ gammaNorm δ (insertTwo (centralPacket ε)) ∧
        gammaNorm δ (centralPacket ε) ≤ (2 * jetConst 1 + 1) * ε ∧
        gammaNorm δ (fun t => insertTwo (centralPacket ε) t - 3 / 5 * ε * atom (3 / 2) t) ≤
          8163 / 10000 * gammaNorm δ (insertTwo (centralPacket ε)) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, hc⟩ := exists_central_scale
  have hC1 := jetConst_nonneg 1
  set η : ℝ := ε / (6400000000 * (jetConst 1 + 1) * (2 * jetConst 1 + 1)) with hη
  refine ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, η, by positivity, ?_, ?_, hc⟩
  · rw [hη, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ 6400000000 * (jetConst 1 + 1) * (2 * jetConst 1 + 1) := by nlinarith
    nlinarith
  · rw [hη, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hC1 hC1]

/-- The four precursor bands and the half-scale band all hold at least `c₀ R/log R` primes. -/
theorem eventually_band_supply {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 < η) :
    ∀ᶠ R : ℝ in atTop,
      η / 4 * (R / Real.log R) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc ⌊1 * R⌋₊ ⌊(1 + η) * R⌋₊).card : ℝ) ∧
      η / 4 * (R / Real.log R) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc ⌊2 * R⌋₊ ⌊(1 + η) * 2 * R⌋₊).card : ℝ) ∧
      η / 4 * (R / Real.log R) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc ⌊3 * (1 + ε) * R⌋₊
          ⌊(1 + η) * (3 * (1 + ε)) * R⌋₊).card : ℝ) ∧
      η / 4 * (R / Real.log R) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc ⌊6 * (1 + ε) * R⌋₊
          ⌊(1 + η) * (6 * (1 + ε)) * R⌋₊).card : ℝ) ∧
      η / 4 * (R / Real.log R) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc ⌊3 / 2 * R⌋₊ ⌊(1 + η) * (3 / 2) * R⌋₊).card : ℝ) := by
  have b : ∀ a : ℝ, 1 ≤ a → ∀ᶠ R : ℝ in atTop, η / 4 * (R / Real.log R) ≤
      ((GaloisForLFunctions.HTGeometry.primesInIoc ⌊a * R⌋₊ ⌊(1 + η) * a * R⌋₊).card : ℝ) := by
    intro a ha
    have h := eventually_card_primes_band (α := a) (β := (1 + η) * a) (by linarith) (by nlinarith)
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with R hR hR1
    have hlog : 0 < Real.log R := Real.log_pos hR1
    have : η / 4 * (R / Real.log R) ≤ ((1 + η) * a - a) / 4 * (R / Real.log R) := by
      have : η ≤ (1 + η) * a - a := by nlinarith
      have : 0 ≤ R / Real.log R := by positivity
      nlinarith
    linarith
  filter_upwards [b 1 le_rfl, b 2 (by norm_num), b (3 * (1 + ε)) (by nlinarith),
    b (6 * (1 + ε)) (by nlinarith), b (3 / 2) (by norm_num)] with R h1 h2 h3 h4 h5
  refine ⟨?_, ?_, h3, h4, h5⟩
  · simpa using h1
  · exact h2

/-- **The macroscopic selection.**  Parameters `δ₀, ε, η` with all central margins, and for every
large `R` a tuple family of `M ≍ R/log R` literal prime tuples in the four bands together with
`⌊(3/5) ε M⌋` primes in the half-scale band. -/
theorem exists_macroscopic_data :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      16 * jetConst 1 * η ≤ ε / (400000000 * (2 * jetConst 1 + 1)) ∧
      (∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
        gammaNorm δ (insertTwo (centralPacket ε)) ≤ 888 / 1000 * gammaNorm δ (centralPacket ε) ∧
        ε / 40 ≤ gammaNorm δ (centralPacket ε) ∧
        ε / 40 ≤ gammaNorm δ (insertTwo (centralPacket ε)) ∧
        gammaNorm δ (centralPacket ε) ≤ (2 * jetConst 1 + 1) * ε ∧
        gammaNorm δ (fun t => insertTwo (centralPacket ε) t - 3 / 5 * ε * atom (3 / 2) t) ≤
          8163 / 10000 * gammaNorm δ (insertTwo (centralPacket ε))) ∧
      ∀ᶠ R : ℝ in atTop, 7 ≤ R ∧ ∃ M : ℕ, 1 ≤ M ∧ η / 16 * (R / Real.log R) ≤ M ∧
        (M : ℝ) ≤ η / 8 * (R / Real.log R) ∧
        ∃ r r' p p' : Fin M → ℕ, StrictMono r ∧ StrictMono r' ∧ StrictMono p ∧ StrictMono p' ∧
          (∀ i, (r i).Prime ∧ (r' i).Prime ∧ (p i).Prime ∧ (p' i).Prime ∧
            InBands R ε η (r i) (r' i) (p i) (p' i)) ∧
          ∃ h : Fin ⌊3 / 5 * ε * M⌋₊ → ℕ, StrictMono h ∧
            ∀ i, (h i).Prime ∧ 3 / 2 * R < h i ∧ (h i : ℝ) ≤ (1 + η) * (3 / 2 * R) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, η, hη, hηε, hηC, hc⟩ := exists_macroscopic_parameters
  refine ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, η, hη, hηε, hηC, hc, ?_⟩
  have hsup := eventually_band_supply hε.le hη
  have hlarge : Tendsto (fun R : ℝ => η / 8 * (R / Real.log R)) atTop atTop :=
    x_log_x_atTop.const_mul_atTop (by positivity)
  filter_upwards [hsup, hlarge.eventually_ge_atTop 2, eventually_ge_atTop (7 : ℝ),
    eventually_gt_atTop (1 : ℝ)] with R ⟨h1, h2, h3, h4, h5⟩ hM2 hR7 hR1
  have hRpos : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos hR1
  set x : ℝ := η / 8 * (R / Real.log R) with hx
  set M : ℕ := ⌊x⌋₊ with hM
  have hx0 : 0 ≤ x := by positivity
  have hMx : (M : ℝ) ≤ x := Nat.floor_le hx0
  have hMx' : x - 1 < M := Nat.sub_one_lt_floor x
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := by linarith
    exact_mod_cast this.le
  have hMle : (M : ℝ) ≤ η / 4 * (R / Real.log R) := by
    have : 0 ≤ R / Real.log R := by positivity
    linarith
  have toNat : ∀ {S : Finset ℕ}, η / 4 * (R / Real.log R) ≤ (S.card : ℝ) → M ≤ S.card := by
    intro S hS
    exact_mod_cast hMle.trans hS
  refine ⟨hR7, M, hM1, by linarith, hMx, ?_⟩
  obtain ⟨r, hrm, hr⟩ := exists_band_enumeration (by positivity) (toNat h1)
  obtain ⟨r', hr'm, hr'⟩ := exists_band_enumeration (by positivity) (toNat h2)
  obtain ⟨p, hpm, hp⟩ := exists_band_enumeration (by positivity) (toNat h3)
  obtain ⟨p', hp'm, hp'⟩ := exists_band_enumeration (by positivity) (toNat h4)
  refine ⟨r, r', p, p', hrm, hr'm, hpm, hp'm, fun i => ?_, ?_⟩
  · obtain ⟨a1, a2, a3⟩ := hr i
    obtain ⟨b1, b2, b3⟩ := hr' i
    obtain ⟨c1, c2, c3⟩ := hp i
    obtain ⟨d1, d2, d3⟩ := hp' i
    refine ⟨a1, b1, c1, d1, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith⟩
  · have hL : ⌊3 / 5 * ε * (M : ℝ)⌋₊ ≤ M := by
      have : 3 / 5 * ε * (M : ℝ) ≤ M := by nlinarith
      exact Nat.floor_le_of_le this
    obtain ⟨h, hhm, hh⟩ := exists_band_enumeration (by positivity) (hL.trans (toNat h5))
    refine ⟨h, hhm, fun i => ?_⟩
    obtain ⟨e1, e2, e3⟩ := hh i
    exact ⟨e1, e2, by linarith⟩

/-- **Card equation (6): the macroscopic aligned source packet.**  For some `δ₀ > 0` and fixed
`ε, η`, every large scale `R` carries `M ≍ R/log R` literal prime tuples in four disjoint bands; the
eight atoms of their `2`-insertions are pairwise distinct across all tuples with coefficients the
literal Möbius values, and for all `0 ≤ δ ≤ δ₀`

`‖D_2 P_R‖_δ² < (4/5) ‖P_R‖_δ²`,   `‖P_R‖_δ², ‖D_2 P_R‖_δ² ≥ (ε/50)² M² R^(-1-δ)`,

so `‖P_R‖_δ² ≫ R^(1-δ)/log² R`. -/
theorem exists_macroscopic_aligned_packet :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      ∀ᶠ R : ℝ in atTop, ∃ M : ℕ, 1 ≤ M ∧ η / 16 * (R / Real.log R) ≤ M ∧
        ∃ r r' p p' : Fin M → ℕ, StrictMono r ∧ StrictMono r' ∧ StrictMono p ∧ StrictMono p' ∧
          (∀ i, (r i).Prime ∧ (r' i).Prime ∧ (p i).Prime ∧ (p' i).Prime ∧
            InBands R ε η (r i) (r' i) (p i) (p' i)) ∧
          (∀ i k, μ (eightAtom (r i) (r' i) (p i) (p' i) k) = eightSign k) ∧
          Function.Injective
            (fun ik : Fin M × Fin 8 => eightAtom (r ik.1) (r' ik.1) (p ik.1) (p' ik.1) ik.2) ∧
          ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
            gammaEnergy δ (insertTwo (tuplePacket r r' p p')) <
              4 / 5 * gammaEnergy δ (tuplePacket r r' p p') ∧
            (ε / 50) ^ 2 * (M : ℝ) ^ 2 * R ^ (-1 - δ) ≤ gammaEnergy δ (tuplePacket r r' p p') ∧
            (ε / 50) ^ 2 * (M : ℝ) ^ 2 * R ^ (-1 - δ) ≤
              gammaEnergy δ (insertTwo (tuplePacket r r' p p')) ∧
            (ε / 50) ^ 2 * (η / 16) ^ 2 * (R ^ (1 - δ) / Real.log R ^ 2) ≤
              gammaEnergy δ (tuplePacket r r' p p') := by
  obtain ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, η, hη, hηε, hηC, hc, hdata⟩ := exists_macroscopic_data
  refine ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, η, hη, hηε, ?_⟩
  filter_upwards [hdata, eventually_gt_atTop (1 : ℝ)] with R hRdata hR1
  obtain ⟨hR7, M, hM1, hMlow, hMup, r, r', p, p', hrm, hr'm, hpm, hp'm, hb, -⟩ := hRdata
  have hR : 0 < R := by linarith
  have hC1 := jetConst_nonneg 1
  have hηC' : 16 * jetConst 1 * η ≤ ε / (40000 * (2 * jetConst 1 + 1)) := by
    refine hηC.trans ?_
    exact div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith)
  have hcentral : ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
      gammaNorm δ (insertTwo (centralPacket ε)) ≤ 888 / 1000 * gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (insertTwo (centralPacket ε)) ∧
      gammaNorm δ (centralPacket ε) ≤ (2 * jetConst 1 + 1) * ε := fun δ hδ =>
    ⟨(hc δ hδ).1, (hc δ hδ).2.1, (hc δ hδ).2.2.1, (hc δ hδ).2.2.2.1⟩
  have hbounds := tuplePacket_bounds hδ₀1 hε hcentral hη.le (by linarith) hηC' hR hM1
    (fun i => (hb i).2.2.2.2)
  refine ⟨M, hM1, hMlow, r, r', p, p', hrm, hr'm, hpm, hp'm, hb, fun i k => ?_, ?_,
    fun δ hδ => ?_⟩
  · obtain ⟨h1, h2, h3, h4, hbi⟩ := hb i
    obtain ⟨b1, -, b3, -, b5, -, b7, -⟩ := hbi
    have c1 : 6 < r i := by exact_mod_cast (show (6 : ℝ) < r i by linarith)
    have c2 : 6 < r' i := by exact_mod_cast (show (6 : ℝ) < r' i by linarith)
    have c3 : 2 < p i := by exact_mod_cast (show (2 : ℝ) < p i by nlinarith)
    have c4 : 2 < p' i := by exact_mod_cast (show (2 : ℝ) < p' i by nlinarith)
    exact moebius_eightAtom h1 h2 h3 h4 c1 c2 c3 c4 k
  · refine eightAtom_injective hR hη.le hηε hε4 hrm.injective hr'm.injective hpm.injective
      hp'm.injective (fun i => ?_) (fun i => (hb i).2.2.2.2)
    obtain ⟨-, h2, -, h4, hbi⟩ := hb i
    obtain ⟨-, -, b3, -, -, -, b7, -⟩ := hbi
    exact ⟨h2, h4, by exact_mod_cast (show (2 : ℝ) < r' i by linarith),
      by exact_mod_cast (show (2 : ℝ) < p' i by nlinarith)⟩
  · obtain ⟨h1, h2, h3⟩ := hbounds δ hδ
    refine ⟨h1, h2, h3, le_trans ?_ h2⟩
    have hlog : 0 < Real.log R := Real.log_pos hR1
    have hM0 : 0 ≤ η / 16 * (R / Real.log R) := by positivity
    have hsq : (η / 16 * (R / Real.log R)) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ hM0 hMlow 2
    have hR2 : R ^ (1 - δ) = R ^ 2 * R ^ (-1 - δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hR]; norm_num; ring_nf
    have hRd : 0 ≤ R ^ (-1 - δ) := by positivity
    calc (ε / 50) ^ 2 * (η / 16) ^ 2 * (R ^ (1 - δ) / Real.log R ^ 2)
        = (ε / 50) ^ 2 * (η / 16 * (R / Real.log R)) ^ 2 * R ^ (-1 - δ) := by
          rw [hR2]; field_simp
      _ ≤ (ε / 50) ^ 2 * (M : ℝ) ^ 2 * R ^ (-1 - δ) := by gcongr

/-! ### The complement of the macroscopic packet -/

/-- The inserted packet is the literal Möbius subsource on its atom set. -/
theorem insertTwo_tuplePacket_eq_literal {R ε η : ℝ} (hR : 0 < R) (hη0 : 0 ≤ η) (hηε : η ≤ ε)
    (hε : ε ≤ 1 / 4) {M : ℕ} {r r' p p' : Fin M → ℕ} (hr : Function.Injective r)
    (hr' : Function.Injective r') (hp : Function.Injective p) (hp' : Function.Injective p')
    (hprime : ∀ i, (r i).Prime ∧ (r' i).Prime ∧ (p i).Prime ∧ (p' i).Prime)
    (hb : ∀ i, InBands R ε η (r i) (r' i) (p i) (p' i)) (h7 : 7 ≤ R) :
    insertTwo (tuplePacket r r' p p') = fun t =>
      ∑ n ∈ Finset.univ.image
        (fun ik : Fin M × Fin 8 => eightAtom (r ik.1) (r' ik.1) (p ik.1) (p' ik.1) ik.2),
        ((μ n : ℤ) : ℝ) * atom n t := by
  have hbig : ∀ i, 6 < r i ∧ 6 < r' i ∧ 2 < p i ∧ 2 < p' i := by
    intro i
    obtain ⟨b1, -, b3, -, b5, -, b7, -⟩ := hb i
    exact ⟨by exact_mod_cast (show (6 : ℝ) < r i by linarith),
      by exact_mod_cast (show (6 : ℝ) < r' i by linarith),
      by exact_mod_cast (show (2 : ℝ) < p i by nlinarith),
      by exact_mod_cast (show (2 : ℝ) < p' i by nlinarith)⟩
  have hinj := eightAtom_injective hR hη0 hηε hε hr hr' hp hp'
    (fun i => ⟨(hprime i).2.1, (hprime i).2.2.2, by have := (hbig i).2.1; omega,
      (hbig i).2.2.2⟩) hb
  funext t
  unfold tuplePacket
  rw [insertTwo_sum]
  simp only
  rw [Finset.sum_image (fun x _ y _ h => hinj h), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [insertTwo_tuple_eq_eight]
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨h1, h2, h3, h4⟩ := hprime i
  obtain ⟨c1, c2, c3, c4⟩ := hbig i
  rw [moebius_eightAtom h1 h2 h3 h4 c1 c2 c3 c4 k]

theorem classLo_bounds {ε : ℝ} (hε : 0 ≤ ε) (k : Fin 8) :
    3 ≤ classLo ε (eightClass k) ∧ classLo ε (eightClass k) ≤ 12 * (1 + ε) := by
  fin_cases k <;> norm_num [eightClass, classLo] <;> first | (constructor <;> linarith) | linarith

theorem eightAtom_mem_Icc {R ε η C : ℝ} (hR : 1 ≤ R) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hC : 12 * (1 + ε) * (1 + η) < C) {r r' p p' : ℕ} (hb : InBands R ε η r r' p p') (k : Fin 8) :
    eightAtom r r' p p' k ∈ Finset.Icc 1 ⌈C * R⌉₊ := by
  obtain ⟨hlo, hhi⟩ := eightAtom_mem_class hb k
  obtain ⟨c1, c2⟩ := classLo_bounds hε k
  have hRpos : 0 < R := by linarith
  rw [Finset.mem_Icc]
  constructor
  · have h3 : 3 * R ≤ classLo ε (eightClass k) * R := mul_le_mul_of_nonneg_right c1 hRpos.le
    have : (1 : ℝ) ≤ (eightAtom r r' p p' k : ℝ) := by linarith
    exact_mod_cast this
  · have h1 : (1 + η) * (classLo ε (eightClass k) * R) ≤ (1 + η) * (12 * (1 + ε) * R) := by
      have := mul_le_mul_of_nonneg_right c2 hRpos.le
      exact mul_le_mul_of_nonneg_left this (by linarith)
    have h2 : (1 + η) * (12 * (1 + ε) * R) ≤ C * R := by
      have : 12 * (1 + ε) * (1 + η) * R ≤ C * R := mul_le_mul_of_nonneg_right hC.le hRpos.le
      linarith
    have : (eightAtom r r' p p' k : ℝ) ≤ C * R := by linarith
    have h := this.trans (Nat.le_ceil (C * R))
    exact_mod_cast h

/-- **Card equation (7): the complement is antiparallel.**  For the macroscopic packets of (6) and
every `C > 12(1+ε)(1+η)`, the inserted packet `D_2 P_R` is a literal Möbius subsource of
`F_(⌈CR⌉)`, and with `Q_R = F_(⌈CR⌉) - D_2 P_R` (the sum over the complementary atoms)

`‖F‖/‖D_2 P‖ ≤ K E(R) log R`,  `⟨D_2P, Q⟩/‖D_2P‖² = -1 + O(E(R) log R)`,
`‖Q‖/‖D_2P‖ = 1 + O(E(R) log R)`,

uniformly for `0 ≤ δ ≤ δ₀`; `E(R) log R → 0` by `tendsto_mertensSaving_mul_log`. -/
theorem macroscopic_complement_antiparallel :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
    ∃ K : ℝ → ℝ → ℝ, (∀ C δ, 0 < K C δ) ∧
      ∀ᶠ R : ℝ in atTop, ∃ M : ℕ, 1 ≤ M ∧ ∃ r r' p p' : Fin M → ℕ,
        (∀ i, (r i).Prime ∧ (r' i).Prime ∧ (p i).Prime ∧ (p' i).Prime ∧
          InBands R ε η (r i) (r' i) (p i) (p' i)) ∧
        ∀ C : ℝ, 12 * (1 + ε) * (1 + η) < C →
          Finset.univ.image (fun ik : Fin M × Fin 8 =>
              eightAtom (r ik.1) (r' ik.1) (p ik.1) (p' ik.1) ik.2) ⊆ Finset.Icc 1 ⌈C * R⌉₊ ∧
          (fun t => mobiusCubicSource ⌈C * R⌉₊ t - insertTwo (tuplePacket r r' p p') t) =
            (fun t => ∑ n ∈ Finset.Icc 1 ⌈C * R⌉₊ \ Finset.univ.image
              (fun ik : Fin M × Fin 8 => eightAtom (r ik.1) (r' ik.1) (p ik.1) (p' ik.1) ik.2),
              ((μ n : ℤ) : ℝ) * atom n t) ∧
          ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
            gammaNorm δ (mobiusCubicSource ⌈C * R⌉₊) ≤
              K C δ * (mertensSaving R * Real.log R) *
                gammaNorm δ (insertTwo (tuplePacket r r' p p')) ∧
            |gammaInner δ (insertTwo (tuplePacket r r' p p'))
                (fun t => mobiusCubicSource ⌈C * R⌉₊ t - insertTwo (tuplePacket r r' p p') t) /
              gammaEnergy δ (insertTwo (tuplePacket r r' p p')) + 1| ≤
              K C δ * (mertensSaving R * Real.log R) ∧
            |gammaNorm δ (fun t => mobiusCubicSource ⌈C * R⌉₊ t - insertTwo (tuplePacket r r' p p') t) /
              gammaNorm δ (insertTwo (tuplePacket r r' p p')) - 1| ≤
              K C δ * (mertensSaving R * Real.log R) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, η, hη, hηε, hηC, hc, hdata⟩ := exists_macroscopic_data
  have hmer : ∀ δ : ℝ, ∃ c : ℝ, 0 < c ∧ (0 ≤ δ → δ < 1 → ∀ N : ℕ, 1 ≤ N →
      gammaNorm δ (mobiusCubicSource N) ≤ c * (N : ℝ) ^ ((1 - δ) / 2) * mertensSaving N) := by
    intro δ
    by_cases h : 0 ≤ δ ∧ δ < 1
    · obtain ⟨c, hc0, hcb⟩ := gammaNorm_mobiusCubicSource_le h.1 h.2
      exact ⟨c, hc0, fun _ _ => hcb⟩
    · exact ⟨1, one_pos, fun h0 h1 => absurd ⟨h0, h1⟩ h⟩
  choose Cm hCm hCmb using hmer
  refine ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, η, hη, hηε,
    fun C δ => Cm δ * (|C| + 1) * (800 / (η * ε)), fun C δ => by
      have := hCm δ; positivity, ?_⟩
  filter_upwards [hdata, eventually_gt_atTop (1 : ℝ)] with R hRdata hR1
  obtain ⟨hR7, M, hM1, hMlow, hMup, r, r', p, p', hrm, hr'm, hpm, hp'm, hb, -⟩ := hRdata
  have hR : 0 < R := by linarith
  have hC1 := jetConst_nonneg 1
  have hηC' : 16 * jetConst 1 * η ≤ ε / (40000 * (2 * jetConst 1 + 1)) := by
    refine hηC.trans ?_
    exact div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith)
  have hcentral : ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
      gammaNorm δ (insertTwo (centralPacket ε)) ≤ 888 / 1000 * gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (insertTwo (centralPacket ε)) ∧
      gammaNorm δ (centralPacket ε) ≤ (2 * jetConst 1 + 1) * ε := fun δ hδ =>
    ⟨(hc δ hδ).1, (hc δ hδ).2.1, (hc δ hδ).2.2.1, (hc δ hδ).2.2.2.1⟩
  have hbounds := tuplePacket_bounds hδ₀1 hε hcentral hη.le (by linarith) hηC' hR hM1
    (fun i => (hb i).2.2.2.2)
  have hlit := insertTwo_tuplePacket_eq_literal hR hη.le hηε hε4 hrm.injective hr'm.injective
    hpm.injective hp'm.injective (fun i => ⟨(hb i).1, (hb i).2.1, (hb i).2.2.1, (hb i).2.2.2.1⟩)
    (fun i => (hb i).2.2.2.2) hR7
  refine ⟨M, hM1, r, r', p, p', hb, fun C hC => ?_⟩
  set S := Finset.univ.image (fun ik : Fin M × Fin 8 =>
    eightAtom (r ik.1) (r' ik.1) (p ik.1) (p' ik.1) ik.2) with hS
  set N : ℕ := ⌈C * R⌉₊ with hN
  have hε0 : 0 ≤ ε := hε.le
  have hC12 : 12 < C := by nlinarith
  have hNR : C * R ≤ N := Nat.le_ceil _
  have hNR' : (N : ℝ) < C * R + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hSsub : S ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [hS, Finset.mem_image] at hn
    obtain ⟨⟨i, k⟩, -, rfl⟩ := hn
    exact eightAtom_mem_Icc hR1.le hε0 hη.le hC (hb i).2.2.2.2 k
  have hcompl : (fun t => mobiusCubicSource N t - insertTwo (tuplePacket r r' p p') t) =
      fun t => ∑ n ∈ Finset.Icc 1 N \ S, ((μ n : ℤ) : ℝ) * atom n t := by
    funext t
    rw [hlit]
    unfold mobiusCubicSource
    rw [← Finset.sum_sdiff hSsub]
    ring
  refine ⟨hSsub, hcompl, fun δ hδ => ?_⟩
  have hδ0 := hδ.1
  have hδ1 : δ < 1 := by linarith [hδ.2]
  have hδ' : 0 < 5 + δ := by linarith
  have fP := gammaFinite_tuplePacket hδ' hR hε.le (fun i => (hb i).2.2.2.2)
  have fD := gammaFinite_insertTwo fP
  have fF : GammaFinite δ (mobiusCubicSource N) := by
    unfold mobiusCubicSource
    exact GammaFinite.sum _ fun n hn => (gammaFinite_atom hδ' (by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this)).smul _
  obtain ⟨-, -, hDlow⟩ := hbounds δ hδ
  -- lower bound for `‖D‖`
  have hDnorm : ε / 50 * (M : ℝ) * R ^ (-(1 + δ) / 2) ≤ gammaNorm δ (insertTwo (tuplePacket r r' p p')) := by
    have h0 : 0 ≤ ε / 50 * (M : ℝ) * R ^ (-(1 + δ) / 2) := by positivity
    have hsq : (ε / 50 * (M : ℝ) * R ^ (-(1 + δ) / 2)) ^ 2 = (ε / 50) ^ 2 * (M : ℝ) ^ 2 * R ^ (-1 - δ) := by
      have hρ2 : (R ^ (-(1 + δ) / 2)) ^ 2 = R ^ (-1 - δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]; norm_num; ring_nf
      rw [mul_pow, mul_pow, hρ2]
    rw [← hsq, ← gammaNorm_sq hδ' fD] at hDlow
    exact (pow_le_pow_iff_left₀ h0 (gammaNorm_nonneg _ _) (by norm_num)).mp hDlow
  set D := gammaNorm δ (insertTwo (tuplePacket r r' p p')) with hDdef
  have hlog : 0 < Real.log R := Real.log_pos hR1
  have hE := mertensSaving_pos R
  -- upper bound for `‖F‖`
  have hF : gammaNorm δ (mobiusCubicSource N) ≤ Cm δ * (|C| + 1) * R ^ ((1 - δ) / 2) * mertensSaving R := by
    have h := hCmb δ hδ0 hδ1 N hN1
    have hNle : (N : ℝ) ≤ (|C| + 1) * R := by
      have : C ≤ |C| := le_abs_self C
      nlinarith
    have hpow : (N : ℝ) ^ ((1 - δ) / 2) ≤ (|C| + 1) * R ^ ((1 - δ) / 2) := by
      calc (N : ℝ) ^ ((1 - δ) / 2) ≤ ((|C| + 1) * R) ^ ((1 - δ) / 2) :=
            Real.rpow_le_rpow (by positivity) hNle (by linarith)
        _ = (|C| + 1) ^ ((1 - δ) / 2) * R ^ ((1 - δ) / 2) :=
            Real.mul_rpow (by positivity) hR.le
        _ ≤ (|C| + 1) * R ^ ((1 - δ) / 2) := by
            gcongr
            exact Real.rpow_le_self_of_one_le (by linarith [abs_nonneg C]) (by linarith)
    have hEN : mertensSaving N ≤ mertensSaving R :=
      mertensSaving_antitone (by linarith) (by nlinarith)
    have hc0 := (hCm δ).le
    have hEN0 := mertensSaving_pos (N : ℝ)
    calc gammaNorm δ (mobiusCubicSource N) ≤ Cm δ * (N : ℝ) ^ ((1 - δ) / 2) * mertensSaving N := h
      _ ≤ Cm δ * ((|C| + 1) * R ^ ((1 - δ) / 2)) * mertensSaving R := by gcongr
      _ = _ := by ring
  -- the ratio bound
  have hratio : gammaNorm δ (mobiusCubicSource N) ≤
      Cm δ * (|C| + 1) * (800 / (η * ε)) * (mertensSaving R * Real.log R) * D := by
    refine hF.trans ?_
    have hMR : η / 16 * (R / Real.log R) * (ε / 50 * R ^ (-(1 + δ) / 2)) ≤ D := by
      calc η / 16 * (R / Real.log R) * (ε / 50 * R ^ (-(1 + δ) / 2))
          ≤ (M : ℝ) * (ε / 50 * R ^ (-(1 + δ) / 2)) := by gcongr
        _ = ε / 50 * (M : ℝ) * R ^ (-(1 + δ) / 2) := by ring
        _ ≤ D := hDnorm
    have hRR : R * R ^ (-(1 + δ) / 2) = R ^ ((1 - δ) / 2) := by
      rw [show (1 - δ) / 2 = 1 + -(1 + δ) / 2 by ring, Real.rpow_add hR, Real.rpow_one]
    have key : Cm δ * (|C| + 1) * R ^ ((1 - δ) / 2) * mertensSaving R =
        Cm δ * (|C| + 1) * (800 / (η * ε)) * (mertensSaving R * Real.log R) *
          (η / 16 * (R / Real.log R) * (ε / 50 * R ^ (-(1 + δ) / 2))) := by
      rw [← hRR]; field_simp; ring
    rw [key]
    have : 0 ≤ Cm δ * (|C| + 1) * (800 / (η * ε)) * (mertensSaving R * Real.log R) := by
      have := hCm δ; positivity
    exact mul_le_mul_of_nonneg_left hMR this
  set K := Cm δ * (|C| + 1) * (800 / (η * ε)) * (mertensSaving R * Real.log R) with hK
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDnorm
  refine ⟨hratio, ?_, ?_⟩
  · -- inner product
    have fQ : GammaFinite δ (fun t => mobiusCubicSource N t - insertTwo (tuplePacket r r' p p') t) :=
      fF.sub fD
    have hinner : gammaInner δ (insertTwo (tuplePacket r r' p p'))
        (fun t => mobiusCubicSource N t - insertTwo (tuplePacket r r' p p') t) =
        gammaInner δ (insertTwo (tuplePacket r r' p p')) (mobiusCubicSource N) -
          gammaEnergy δ (insertTwo (tuplePacket r r' p p')) := by
      rw [gammaInner_comm, show (fun t => mobiusCubicSource N t - insertTwo (tuplePacket r r' p p') t) =
        fun t => 1 * mobiusCubicSource N t + (-1) * insertTwo (tuplePacket r r' p p') t by
          funext t; ring,
        gammaInner_add_left hδ' (fF.smul 1) (fD.smul (-1)) fD,
        gammaInner_smul_left hδ' fF fD, gammaInner_smul_left hδ' fD fD, gammaInner_comm, gammaEnergy]
      ring
    have hEn : gammaEnergy δ (insertTwo (tuplePacket r r' p p')) = D ^ 2 := by
      rw [hDdef, gammaNorm_sq hδ' fD]
    have hD2 : 0 < D ^ 2 := pow_pos hDpos 2
    have hsimp : (gammaInner δ (insertTwo (tuplePacket r r' p p')) (mobiusCubicSource N) - D ^ 2) /
        D ^ 2 + 1 = gammaInner δ (insertTwo (tuplePacket r r' p p')) (mobiusCubicSource N) / D ^ 2 := by
      field_simp; ring
    rw [hinner, hEn, hsimp, abs_div, abs_of_pos hD2]
    have hcs := abs_gammaInner_le hδ' fD fF
    rw [← hDdef] at hcs
    calc |gammaInner δ (insertTwo (tuplePacket r r' p p')) (mobiusCubicSource N)| / D ^ 2
        ≤ D * gammaNorm δ (mobiusCubicSource N) / D ^ 2 := by gcongr
      _ = gammaNorm δ (mobiusCubicSource N) / D := by field_simp
      _ ≤ K * D / D := by gcongr
      _ = Cm δ * (|C| + 1) * (800 / (η * ε)) * (mertensSaving R * Real.log R) := by
          rw [hK]; field_simp
  · -- norm ratio
    have fQ : GammaFinite δ (fun t => mobiusCubicSource N t - insertTwo (tuplePacket r r' p p') t) :=
      fF.sub fD
    have h := abs_gammaNorm_sub_le hδ' fQ fD.neg
    rw [gammaNorm_neg hδ' fD, ← hDdef,
      show (fun t => (mobiusCubicSource N t - insertTwo (tuplePacket r r' p p') t) -
        -insertTwo (tuplePacket r r' p p') t) = mobiusCubicSource N by funext t; ring] at h
    rw [show gammaNorm δ (fun t => mobiusCubicSource N t - insertTwo (tuplePacket r r' p p') t) / D - 1 =
      (gammaNorm δ (fun t => mobiusCubicSource N t - insertTwo (tuplePacket r r' p p') t) - D) / D by
        field_simp, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    refine h.trans ?_
    rw [hK] at hratio
    linarith

/-! ### The literal half-scale compensator -/

/-- `‖P - M·B^R‖_δ ≤ M · 16 C_1 η R^(-(1+δ)/2)`. -/
theorem gammaNorm_tuplePacket_sub_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {R ε η : ℝ} (hR : 0 < R)
    (hε : 0 ≤ ε) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {M : ℕ} {r r' p p' : Fin M → ℕ}
    (hb : ∀ i, InBands R ε η (r i) (r' i) (p i) (p' i)) :
    gammaNorm δ (fun t => tuplePacket r r' p p' t - (M : ℝ) * dilate R (centralPacket ε) t) ≤
      (M : ℝ) * (16 * jetConst 1 * η * R ^ (-(1 + δ) / 2)) := by
  have hδ' : 0 < 5 + δ := by linarith
  have fB : GammaFinite δ (dilate R (centralPacket ε)) :=
    (gammaFinite_centralPacket hδ' hε).dilate hR
  have fTi : ∀ i : Fin M, GammaFinite δ (fun t => twoDipolePrecursor (3 * (r i : ℝ)) (p i)
      (3 * (r' i : ℝ)) (p' i) t - dilate R (centralPacket ε) t) := by
    intro i
    obtain ⟨h1, -, h3, -, h5, -, h7, -⟩ := hb i
    exact (gammaFinite_twoDipolePrecursor hδ' (by linarith) (by nlinarith) (by linarith)
      (by nlinarith)).sub fB
  have e : (fun t => tuplePacket r r' p p' t - (M : ℝ) * dilate R (centralPacket ε) t) =
      fun t => ∑ i : Fin M, (twoDipolePrecursor (3 * (r i : ℝ)) (p i) (3 * (r' i : ℝ)) (p' i) t -
        dilate R (centralPacket ε) t) := by
    funext t
    simp only [tuplePacket, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [e]
  refine (gammaNorm_sum_le hδ' _ fun i _ => fTi i).trans ?_
  calc ∑ i : Fin M, gammaNorm δ (fun t => twoDipolePrecursor (3 * (r i : ℝ)) (p i)
        (3 * (r' i : ℝ)) (p' i) t - dilate R (centralPacket ε) t)
      ≤ ∑ _i : Fin M, 16 * jetConst 1 * η * R ^ (-(1 + δ) / 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb i
        exact gammaNorm_tuple_sub_central hδ0 hδ1 hR hε hη0 hη1 h1 h2 h3 h4 h5 h6 h7 h8
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The analytic core of (9): with the central margins, a literal half-band of `L ≈ (3/5) ε M`
primes compensates the inserted packet down to norm ratio `0.81649 < √(2/3)`. -/
theorem halfScale_core {δ R ε η : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 0 < R) (hε : 0 < ε)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hηs : 36 * jetConst 1 * η ≤ ε / 100000000)
    (hDl : ε / 40 ≤ gammaNorm δ (insertTwo (centralPacket ε)))
    (hCε : gammaNorm δ (fun t => insertTwo (centralPacket ε) t - 3 / 5 * ε * atom (3 / 2) t) ≤
      8163 / 10000 * gammaNorm δ (insertTwo (centralPacket ε)))
    {M : ℕ} (hMε : 1000000 / ε ≤ (M : ℝ)) {r r' p p' : Fin M → ℕ}
    (hb : ∀ i, InBands R ε η (r i) (r' i) (p i) (p' i))
    {L : ℕ} (hLM : (L : ℝ) ≤ M) (hLdev : |(L : ℝ) - 3 / 5 * ε * M| ≤ 1) {h : Fin L → ℕ}
    (hh : ∀ j, 3 / 2 * R < h j ∧ (h j : ℝ) ≤ (1 + η) * (3 / 2 * R)) :
    gammaNorm δ (fun t => insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t) ≤
        81649 / 100000 * gammaNorm δ (insertTwo (tuplePacket r r' p p')) ∧
      0 < gammaNorm δ (insertTwo (tuplePacket r r' p p')) := by
  have hδ' : 0 < 5 + δ := by linarith
  have hC1 := jetConst_nonneg 1
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hMε
  have hρ0 : 0 < R ^ (-(1 + δ) / 2) := Real.rpow_pos_of_pos hR _
  have fP := gammaFinite_tuplePacket hδ' hR hε.le hb
  have fD := gammaFinite_insertTwo fP
  have fBε := gammaFinite_centralPacket hδ' hε.le
  have fDBε := gammaFinite_insertTwo fBε
  have fA := gammaFinite_atom hδ' (by positivity : (0 : ℝ) < R * (3 / 2))
  have fA1 := gammaFinite_atom hδ' (by norm_num : (0 : ℝ) < 3 / 2)
  have fH : ∀ j, GammaFinite δ (atom (h j)) := fun j =>
    gammaFinite_atom hδ' (by have := (hh j).1; linarith)
  have fU : GammaFinite δ (fun t => (M : ℝ) * dilate R (insertTwo (centralPacket ε)) t) :=
    (fDBε.dilate hR).smul _
  have fW : GammaFinite δ (fun t => (M : ℝ) * dilate R
      (fun t => insertTwo (centralPacket ε) t - 3 / 5 * ε * atom (3 / 2) t) t) :=
    ((fDBε.sub (fA1.smul _)).dilate hR).smul _
  have nU : gammaNorm δ (fun t => (M : ℝ) * dilate R (insertTwo (centralPacket ε)) t) =
      (M : ℝ) * (R ^ (-(1 + δ) / 2) * gammaNorm δ (insertTwo (centralPacket ε))) := by
    rw [gammaNorm_smul hδ' (fDBε.dilate hR), abs_of_nonneg hM0, gammaNorm_dilate hR]
  have nW : gammaNorm δ (fun t => (M : ℝ) * dilate R
      (fun t => insertTwo (centralPacket ε) t - 3 / 5 * ε * atom (3 / 2) t) t) ≤
      (M : ℝ) * (R ^ (-(1 + δ) / 2) * (8163 / 10000 * gammaNorm δ (insertTwo (centralPacket ε)))) := by
    rw [gammaNorm_smul hδ' ((fDBε.sub (fA1.smul _)).dilate hR), abs_of_nonneg hM0,
      gammaNorm_dilate hR]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCε hρ0.le) hM0
  -- `D_2 P` is close to `U`
  have hPU := gammaNorm_tuplePacket_sub_le hδ0 hδ1 hR hε.le hη0 hη1 hb
  have hDU : gammaNorm δ (fun t => insertTwo (tuplePacket r r' p p') t -
      (M : ℝ) * dilate R (insertTwo (centralPacket ε)) t) ≤
      2 * ((M : ℝ) * (16 * jetConst 1 * η * R ^ (-(1 + δ) / 2))) := by
    have e : (fun t => insertTwo (tuplePacket r r' p p') t -
        (M : ℝ) * dilate R (insertTwo (centralPacket ε)) t) =
        insertTwo (fun t => tuplePacket r r' p p' t - (M : ℝ) * dilate R (centralPacket ε) t) := by
      funext t; unfold insertTwo dilate; ring_nf
    rw [e]
    exact (gammaNorm_insertTwo_le hδ0 (fP.sub ((fBε.dilate hR).smul _))).trans (by linarith)
  -- the half band
  have hHsum : gammaNorm δ (fun t => ∑ j, atom (h j) t - (L : ℝ) * atom (R * (3 / 2)) t) ≤
      (L : ℝ) * (4 * jetConst 1 * η * R ^ (-(1 + δ) / 2)) := by
    have e : (fun t => ∑ j, atom (h j) t - (L : ℝ) * atom (R * (3 / 2)) t) =
        fun t => ∑ j : Fin L, (atom (h j) t - atom (R * (3 / 2)) t) := by
      funext t
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [e]
    refine (gammaNorm_sum_le hδ' _ fun j _ => (fH j).sub fA).trans ?_
    calc ∑ j : Fin L, gammaNorm δ (fun t => atom (h j) t - atom (R * (3 / 2)) t)
        ≤ ∑ _j : Fin L, 4 * jetConst 1 * η * R ^ (-(1 + δ) / 2) := by
          refine Finset.sum_le_sum fun j _ => ?_
          obtain ⟨e2, e3⟩ := hh j
          exact gammaNorm_atom_band hδ0 hδ1 hR (by linarith) (by linarith) (by linarith) hη0 hη1
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hA32 : gammaNorm δ (atom (R * (3 / 2))) ≤ R ^ (-(1 + δ) / 2) := by
    refine (gammaNorm_atom_le hδ0 (by positivity)).trans ?_
    exact Real.rpow_le_rpow_of_nonpos hR (le_mul_of_one_le_right hR.le (by norm_num))
      (by linarith)
  -- `S - W`
  have hWsplit : (fun t => (M : ℝ) * dilate R
      (fun t => insertTwo (centralPacket ε) t - 3 / 5 * ε * atom (3 / 2) t) t) =
      fun t => (M : ℝ) * dilate R (insertTwo (centralPacket ε)) t -
        3 / 5 * ε * (M : ℝ) * atom (R * (3 / 2)) t := by
    funext t
    unfold dilate
    rw [← atom_scale (3 / 2) R t]
    ring
  rw [hWsplit] at nW fW
  have hSW : gammaNorm δ (fun t => (insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t) -
      ((M : ℝ) * dilate R (insertTwo (centralPacket ε)) t -
          3 / 5 * ε * (M : ℝ) * atom (R * (3 / 2)) t)) ≤
      2 * ((M : ℝ) * (16 * jetConst 1 * η * R ^ (-(1 + δ) / 2))) +
        (L : ℝ) * (4 * jetConst 1 * η * R ^ (-(1 + δ) / 2)) + R ^ (-(1 + δ) / 2) := by
    have e : (fun t => (insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t) -
        ((M : ℝ) * dilate R (insertTwo (centralPacket ε)) t -
          3 / 5 * ε * (M : ℝ) * atom (R * (3 / 2)) t)) =
        fun t => ((insertTwo (tuplePacket r r' p p') t -
            (M : ℝ) * dilate R (insertTwo (centralPacket ε)) t) +
          (-1) * (∑ j, atom (h j) t - (L : ℝ) * atom (R * (3 / 2)) t)) +
          (3 / 5 * ε * (M : ℝ) - (L : ℝ)) * atom (R * (3 / 2)) t := by
      funext t; ring
    rw [e]
    have f1 : GammaFinite δ (fun t => insertTwo (tuplePacket r r' p p') t -
        (M : ℝ) * dilate R (insertTwo (centralPacket ε)) t) := fD.sub fU
    have f2 : GammaFinite δ (fun t => ∑ j, atom (h j) t - (L : ℝ) * atom (R * (3 / 2)) t) :=
      (GammaFinite.sum _ fun j _ => fH j).sub (fA.smul _)
    refine (gammaNorm_add_le hδ' (f1.add (f2.smul _)) (fA.smul _)).trans ?_
    refine add_le_add ((gammaNorm_add_le hδ' f1 (f2.smul _)).trans (add_le_add hDU ?_)) ?_
    · rw [gammaNorm_smul hδ' f2, abs_neg, abs_one, one_mul]; exact hHsum
    · rw [gammaNorm_smul hδ' fA, abs_sub_comm]
      calc |(L : ℝ) - 3 / 5 * ε * (M : ℝ)| * gammaNorm δ (atom (R * (3 / 2)))
          ≤ 1 * R ^ (-(1 + δ) / 2) := mul_le_mul hLdev hA32 (gammaNorm_nonneg _ _) zero_le_one
        _ = R ^ (-(1 + δ) / 2) := one_mul _
  -- two-sided norms
  have fS : GammaFinite δ (fun t => insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t) :=
    fD.sub (GammaFinite.sum _ fun j _ => fH j)
  have nS := gammaNorm_near (e := 2 * ((M : ℝ) * (16 * jetConst 1 * η * R ^ (-(1 + δ) / 2))) +
        (L : ℝ) * (4 * jetConst 1 * η * R ^ (-(1 + δ) / 2)) + R ^ (-(1 + δ) / 2)) hδ' fS fW.neg (by
    have e : (fun t => (insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t) +
        -((M : ℝ) * dilate R (insertTwo (centralPacket ε)) t -
          3 / 5 * ε * (M : ℝ) * atom (R * (3 / 2)) t)) =
        fun t => (insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t) -
          ((M : ℝ) * dilate R (insertTwo (centralPacket ε)) t -
            3 / 5 * ε * (M : ℝ) * atom (R * (3 / 2)) t) := by
      funext t; ring
    rw [e]; exact hSW)
  rw [gammaNorm_neg hδ' fW] at nS
  have nD := gammaNorm_near (e := 2 * ((M : ℝ) * (16 * jetConst 1 * η * R ^ (-(1 + δ) / 2))))
      hδ' fD fU.neg (by
    have e : (fun t => insertTwo (tuplePacket r r' p p') t +
        -((M : ℝ) * dilate R (insertTwo (centralPacket ε)) t)) =
        fun t => insertTwo (tuplePacket r r' p p') t -
          (M : ℝ) * dilate R (insertTwo (centralPacket ε)) t := by funext t; ring
    rw [e]; exact hDU)
  rw [gammaNorm_neg hδ' fU, nU] at nD
  -- scalar bookkeeping in `Y = M ρ` and `g = ‖D_2 B_ε‖`
  set g := gammaNorm δ (insertTwo (centralPacket ε)) with hg
  set ρ := R ^ (-(1 + δ) / 2) with hρ
  have hY : 0 < (M : ℝ) * ρ := mul_pos hMpos hρ0
  have hηY : (M : ℝ) * ρ * (36 * jetConst 1 * η) ≤ (M : ℝ) * ρ * (ε / 100000000) :=
    mul_le_mul_of_nonneg_left hηs hY.le
  have hLterm : (L : ℝ) * (4 * jetConst 1 * η * ρ) ≤ (M : ℝ) * (4 * jetConst 1 * η * ρ) :=
    mul_le_mul_of_nonneg_right hLM (by positivity)
  have hρM : ρ ≤ (M : ℝ) * ρ * (ε / 1000000) := by
    have h1 : 1 ≤ (M : ℝ) * (ε / 1000000) := by
      rw [div_le_iff₀ hε] at hMε
      have : 1000000 ≤ (M : ℝ) * ε := by linarith
      rw [← mul_div_assoc, le_div_iff₀ (by norm_num)]; linarith
    calc ρ = 1 * ρ := (one_mul ρ).symm
      _ ≤ (M : ℝ) * (ε / 1000000) * ρ := mul_le_mul_of_nonneg_right h1 hρ0.le
      _ = (M : ℝ) * ρ * (ε / 1000000) := by ring
  have hYg : (M : ℝ) * ρ * (ε / 40) ≤ (M : ℝ) * ρ * g := mul_le_mul_of_nonneg_left hDl hY.le
  have hS_up : gammaNorm δ (fun t => insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t) ≤
      (M : ℝ) * ρ * (8163 / 10000 * g) + (M : ℝ) * ρ * (ε / 100000000) + ρ := by
    have e1 : 2 * ((M : ℝ) * (16 * jetConst 1 * η * ρ)) + (M : ℝ) * (4 * jetConst 1 * η * ρ) =
        (M : ℝ) * ρ * (36 * jetConst 1 * η) := by ring
    have e2 : (M : ℝ) * (ρ * (8163 / 10000 * g)) = (M : ℝ) * ρ * (8163 / 10000 * g) := by ring
    linarith [nS.2]
  have hD_low : (M : ℝ) * ρ * g - (M : ℝ) * ρ * (ε / 100000000) ≤
      gammaNorm δ (insertTwo (tuplePacket r r' p p')) := by
    have e1 : 2 * ((M : ℝ) * (16 * jetConst 1 * η * ρ)) ≤ (M : ℝ) * ρ * (36 * jetConst 1 * η) := by
      have : 0 ≤ (M : ℝ) * ρ * (4 * jetConst 1 * η) := by positivity
      linarith
    have e2 : (M : ℝ) * (ρ * g) = (M : ℝ) * ρ * g := by ring
    linarith [nD.1]
  have hYε : 0 < (M : ℝ) * ρ * ε := by positivity
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- **Card equation (9): a literal second-stage prime compensator.**  Removing the
`⌊(3/5) ε M⌋` half-scale prime atoms (literal coefficient `μ(p) = -1`) from the inserted packet
lowers its energy below `2/3`, hence below `8/15` of the precursor energy, for all
`0 ≤ δ ≤ δ₀`. -/
theorem exists_halfScale_compensated_packet :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      ∀ᶠ R : ℝ in atTop, ∃ M : ℕ, 1 ≤ M ∧ η / 16 * (R / Real.log R) ≤ M ∧
        ∃ r r' p p' : Fin M → ℕ, StrictMono r ∧ StrictMono r' ∧ StrictMono p ∧ StrictMono p' ∧
          (∀ i, (r i).Prime ∧ (r' i).Prime ∧ (p i).Prime ∧ (p' i).Prime ∧
            InBands R ε η (r i) (r' i) (p i) (p' i)) ∧
          ∃ h : Fin ⌊3 / 5 * ε * M⌋₊ → ℕ, StrictMono h ∧
            (∀ j, (h j).Prime ∧ μ (h j) = -1 ∧ 3 / 2 * R < h j ∧ (h j : ℝ) ≤ (1 + η) * (3 / 2 * R) ∧
              ∀ i k, h j ≠ eightAtom (r i) (r' i) (p i) (p' i) k) ∧
            |(⌊3 / 5 * ε * M⌋₊ : ℝ) - 3 / 5 * ε * M| ≤ 1 ∧
            ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
              gammaEnergy δ (fun t => insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t) <
                2 / 3 * gammaEnergy δ (insertTwo (tuplePacket r r' p p')) ∧
              2 / 3 * gammaEnergy δ (insertTwo (tuplePacket r r' p p')) <
                8 / 15 * gammaEnergy δ (tuplePacket r r' p p') := by
  obtain ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, η, hη, hηε, hηC, hc, hdata⟩ := exists_macroscopic_data
  refine ⟨δ₀, hδ₀, hδ₀1, ε, hε, hε4, η, hη, hηε, ?_⟩
  have hlarge : Tendsto (fun R : ℝ => η / 16 * (R / Real.log R)) atTop atTop :=
    x_log_x_atTop.const_mul_atTop (by positivity)
  filter_upwards [hdata, eventually_gt_atTop (1 : ℝ), hlarge.eventually_ge_atTop (1000000 / ε)]
    with R hRdata hR1 hMbig
  obtain ⟨hR7, M, hM1, hMlow, hMup, r, r', p, p', hrm, hr'm, hpm, hp'm, hb, h, hhm, hh⟩ := hRdata
  have hR : 0 < R := by linarith
  have hC1 := jetConst_nonneg 1
  have hηC' : 16 * jetConst 1 * η ≤ ε / (40000 * (2 * jetConst 1 + 1)) := by
    refine hηC.trans ?_
    exact div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith)
  have hηs : 36 * jetConst 1 * η ≤ ε / 100000000 := by
    have : 16 * jetConst 1 * η ≤ ε / 400000000 :=
      hηC.trans (div_le_div_of_nonneg_left hε.le (by norm_num)
        (le_mul_of_one_le_right (by norm_num) (by linarith)))
    linarith
  have hcentral : ∀ δ ∈ Set.Icc (0 : ℝ) δ₀,
      gammaNorm δ (insertTwo (centralPacket ε)) ≤ 888 / 1000 * gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (centralPacket ε) ∧
      ε / 40 ≤ gammaNorm δ (insertTwo (centralPacket ε)) ∧
      gammaNorm δ (centralPacket ε) ≤ (2 * jetConst 1 + 1) * ε := fun δ hδ =>
    ⟨(hc δ hδ).1, (hc δ hδ).2.1, (hc δ hδ).2.2.1, (hc δ hδ).2.2.2.1⟩
  have hbounds := tuplePacket_bounds hδ₀1 hε hcentral hη.le (by linarith) hηC' hR hM1
    (fun i => (hb i).2.2.2.2)
  have hMε : 1000000 / ε ≤ (M : ℝ) := hMbig.trans hMlow
  have hLM : ((⌊3 / 5 * ε * (M : ℝ)⌋₊ : ℕ) : ℝ) ≤ M := by
    have : 3 / 5 * ε * (M : ℝ) ≤ M := by
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith
    exact_mod_cast Nat.floor_le_of_le this
  have hLdev : |((⌊3 / 5 * ε * (M : ℝ)⌋₊ : ℕ) : ℝ) - 3 / 5 * ε * M| ≤ 1 := by
    have hx : 0 ≤ 3 / 5 * ε * (M : ℝ) := by positivity
    rw [abs_le]
    constructor
    · linarith [Nat.sub_one_lt_floor (3 / 5 * ε * (M : ℝ))]
    · linarith [Nat.floor_le hx]
  refine ⟨M, hM1, hMlow, r, r', p, p', hrm, hr'm, hpm, hp'm, hb, h, hhm, fun j => ?_, hLdev,
    fun δ hδ => ?_⟩
  · obtain ⟨e1, e2, e3⟩ := hh j
    refine ⟨e1, moebius_prime _ e1, e2, e3, fun i k => ?_⟩
    have hk := (eightAtom_mem_class (hb i).2.2.2.2 k).1
    have hcl := (classLo_bounds hε.le k).1
    intro heq
    have : (h j : ℝ) = eightAtom (r i) (r' i) (p i) (p' i) k := by exact_mod_cast heq
    have h3 : 3 * R ≤ classLo ε (eightClass k) * R := mul_le_mul_of_nonneg_right hcl hR.le
    have : (1 + η) * (3 / 2 * R) < 3 * R := by nlinarith
    linarith
  · obtain ⟨hr45, -, -⟩ := hbounds δ hδ
    obtain ⟨-, -, hDl, -, hCε⟩ := hc δ hδ
    have hδ1 : δ ≤ 1 := hδ.2.trans (hδ₀1.trans (by norm_num))
    have hδ' : 0 < 5 + δ := by linarith [hδ.1]
    obtain ⟨key, hDpos⟩ := halfScale_core hδ.1 hδ1 hR hε hη.le (by linarith) hηs hDl hCε hMε
      (fun i => (hb i).2.2.2.2) hLM hLdev (fun j => ⟨(hh j).2.1, (hh j).2.2⟩)
    have fP := gammaFinite_tuplePacket hδ' hR hε.le (fun i => (hb i).2.2.2.2)
    have fD := gammaFinite_insertTwo fP
    have fS : GammaFinite δ (fun t => insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t) :=
      fD.sub (GammaFinite.sum _ fun j _ => gammaFinite_atom hδ' (by
        have := (hh j).2.1; linarith))
    rw [← gammaNorm_sq hδ' fS, ← gammaNorm_sq hδ' fD]
    have h0 := gammaNorm_nonneg δ (fun t => insertTwo (tuplePacket r r' p p') t - ∑ j, atom (h j) t)
    have hsq := pow_le_pow_left₀ h0 key 2
    have hD2 : 0 < gammaNorm δ (insertTwo (tuplePacket r r' p p')) ^ 2 := by positivity
    refine ⟨?_, ?_⟩
    · have : (81649 / 100000 * gammaNorm δ (insertTwo (tuplePacket r r' p p'))) ^ 2 <
          2 / 3 * gammaNorm δ (insertTwo (tuplePacket r r' p p')) ^ 2 := by
        rw [mul_pow]; exact mul_lt_mul_of_pos_right (by norm_num) hD2
      linarith
    · rw [gammaNorm_sq hδ' fD]
      linarith

end RHTower.CubicGamma
