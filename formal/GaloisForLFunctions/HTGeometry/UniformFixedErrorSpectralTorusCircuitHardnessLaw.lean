import GaloisForLFunctions.HTGeometry.ContinuousCircuitMetricEntropyLaw
import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
import GaloisForLFunctions.HTGeometry.BesselOrderFactorialGrowth
import GaloisForLFunctions.HTGeometry.HierarchicalResonanceBreaking

/-!
# Uniform fixed-error circuit hardness on every spectral torus

Boolean spectral reflections form `2^(2^n)` endpoints at pairwise operator
distance two in every fixed eigenbasis. Quantitative quarter-nets for all
continuous two-qubit circuits of gate count at most `s` therefore leave one
reflection at distance greater than `1/2` whenever circuit entropy is smaller
than carrier entropy.

The final theorem proves this entropy separation unconditionally for every
polynomial gate budget `n^q`, eventually in qubit count. This replaces the
dimension-dependent error obtained from compactness by one common physical
operator-norm error, uniformly over all eigenbases.
-/

open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem exists_bool_far_from_small_net
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [PseudoMetricSpace X]
    (p : (ι → Bool) → X)
    (hsep : ∀ {b c : ι → Bool}, b ≠ c → dist (p b) (p c) = 2)
    (net : Finset X)
    (hcard : net.card < 2 ^ Fintype.card ι) :
    ∃ b : ι → Bool, ∀ x ∈ net, (3 / 4 : ℝ) < dist (p b) x := by
  classical
  by_contra h
  push Not at h
  choose f hfmem hfdist using h
  let g : (ι → Bool) → {x // x ∈ net} := fun b => ⟨f b, hfmem b⟩
  have hg : Function.Injective g := by
    intro b c hbc
    by_contra hne
    have htwo := hsep hne
    have htri := dist_triangle (p b) (f b) (p c)
    have hfc : f b = f c := congrArg Subtype.val hbc
    have hle : dist (p b) (p c) ≤ (3 / 4 : ℝ) + 3 / 4 := by
      calc
        dist (p b) (p c) ≤ dist (p b) (f b) + dist (f b) (p c) := htri
        _ = dist (p b) (f b) + dist (f c) (p c) := by rw [hfc]
        _ = dist (p b) (f b) + dist (p c) (f c) := by rw [dist_comm (f c)]
        _ ≤ (3 / 4 : ℝ) + 3 / 4 := add_le_add (hfdist b) (hfdist c)
    rw [htwo] at hle
    norm_num at hle
  have hle := Fintype.card_le_of_injective g hg
  have hdomain : Fintype.card (ι → Bool) = 2 ^ Fintype.card ι := by simp
  have hcodomain : Fintype.card {x // x ∈ net} = net.card := by simp
  rw [hdomain, hcodomain] at hle
  exact (Nat.not_le_of_lt hcard) hle

def qubitBooleanReflection {n : ℕ}
    (b : (Fin n → Bool) → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.diagonal fun i ↦ if b i then -1 else 1

def qubitSpectralBooleanReflection {n : ℕ}
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (b : (Fin n → Bool) → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
    qubitBooleanReflection b *
    star (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)

theorem qubitBooleanReflection_mem_unitary {n : ℕ}
    (b : (Fin n → Bool) → Bool) :
    qubitBooleanReflection b ∈
      unitary (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  exact StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general _ (fun i ↦ by
    cases b i <;> norm_num)

theorem qubitSpectralBooleanReflection_mem_unitary {n : ℕ}
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (b : (Fin n → Bool) → Bool) :
    qubitSpectralBooleanReflection V b ∈
      unitary (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  exact mul_mem (mul_mem V.2 (qubitBooleanReflection_mem_unitary b))
    (Unitary.star_mem V.2)

private theorem boolReflectionCoordinateDifference_norm
    {b c : Bool} (hbc : b ≠ c) :
    ‖((if b then (-1 : ℂ) else 1) -
      (if c then (-1 : ℂ) else 1))‖ = 2 := by
  cases b <;> cases c
  · simp at hbc
  · norm_num [Complex.norm_def, Complex.normSq_ofReal]
  · norm_num [Complex.norm_def, Complex.normSq_ofReal]
  · simp at hbc

theorem dist_qubitBooleanReflection_eq_two {n : ℕ}
    {b c : (Fin n → Bool) → Bool} (hbc : b ≠ c) :
    dist (qubitBooleanReflection b) (qubitBooleanReflection c) = 2 := by
  rw [dist_eq_norm]
  have hdiag :
      qubitBooleanReflection b - qubitBooleanReflection c =
        Matrix.diagonal (fun i ↦
          (if b i then (-1 : ℂ) else 1) -
          (if c i then (-1 : ℂ) else 1)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [qubitBooleanReflection]
    · simp [qubitBooleanReflection, hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    intro i
    cases hbi : b i <;> cases hci : c i <;>
      norm_num [Complex.norm_def, Complex.normSq_ofReal]
  · have hpoint : ∃ i, b i ≠ c i := by
      by_contra h
      push Not at h
      exact hbc (funext h)
    obtain ⟨i, hi⟩ := hpoint
    have hle := norm_le_pi_norm
      (fun i ↦
        (if b i then (-1 : ℂ) else 1) -
        (if c i then (-1 : ℂ) else 1)) i
    rw [boolReflectionCoordinateDifference_norm hi] at hle
    exact hle

theorem dist_qubitSpectralBooleanReflection_eq_two {n : ℕ}
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    {b c : (Fin n → Bool) → Bool} (hbc : b ≠ c) :
    dist (qubitSpectralBooleanReflection V b)
      (qubitSpectralBooleanReflection V c) = 2 := by
  rw [dist_eq_norm]
  have hdiff :
      qubitSpectralBooleanReflection V b -
          qubitSpectralBooleanReflection V c =
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
          (qubitBooleanReflection b - qubitBooleanReflection c) *
          star (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    simp only [qubitSpectralBooleanReflection]
    noncomm_ring
  rw [hdiff, l2_opNorm_unitary_conj_eq V.2]
  simpa [dist_eq_norm] using dist_qubitBooleanReflection_eq_two hbc

theorem exists_qubitSpectralBooleanReflection_exactCircuit_fixedError
    {n R : ℕ} (hR : 0 < R)
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hEntropy :
      ((n * n : ℕ) : ℝ) ^ R *
          (1 + 16 * (R : ℝ)) ^ (32 * R) <
        ((2 ^ (2 ^ n) : ℕ) : ℝ)) :
    ∃ b : (Fin n → Bool) → Bool,
      ∀ A : TwoQubitArchitecture n R,
      ∀ gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
        (1 / 2 : ℝ) <
          ‖qubitSpectralBooleanReflection V b -
            ((A.contraction gates :
              Matrix.unitaryGroup (Fin n → Bool) ℂ) :
                Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  classical
  obtain ⟨net, hnetCover, hnetCard⟩ :=
    exists_exactContinuousTwoQubitCircuit_operatorNet_card_le
      (n := n) (R := R) hR (ε := (1 / 4 : ℝ)) (by norm_num)
  norm_num at hnetCard
  have hnetCard' :
      (net.card : ℝ) < ((2 ^ (2 ^ n) : ℕ) : ℝ) := by
    refine hnetCard.trans_lt ?_
    norm_num [Nat.cast_mul, div_eq_mul_inv] at hEntropy ⊢
    ring_nf at hEntropy ⊢
    exact hEntropy
  have hcard : net.card < 2 ^ (2 ^ n) := by
    exact_mod_cast hnetCard'
  let matrixNet :
      Finset (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
    net.image Subtype.val
  have hmatrixNetCard : matrixNet.card = net.card := by
    exact Finset.card_image_of_injective net Subtype.val_injective
  obtain ⟨b, hb⟩ := exists_bool_far_from_small_net
    (p := qubitSpectralBooleanReflection V)
    (fun hbc => dist_qubitSpectralBooleanReflection_eq_two V hbc)
    matrixNet (by simpa [hmatrixNetCard] using hcard)
  refine ⟨b, ?_⟩
  intro A gates
  obtain ⟨W, hW, hCW⟩ := hnetCover A gates
  have hWmatrix :
      (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈ matrixNet := by
    exact Finset.mem_image.mpr ⟨W, hW, rfl⟩
  have hfar := hb W hWmatrix
  by_contra h
  push Not at h
  have htargetCircuit :
      dist (qubitSpectralBooleanReflection V b)
          (((A.contraction gates :
            Matrix.unitaryGroup (Fin n → Bool) ℂ) :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) ≤ (1 / 2 : ℝ) := by
    simpa [dist_eq_norm] using h
  have htargetNet :
      dist (qubitSpectralBooleanReflection V b)
        (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤ (3 / 4 : ℝ) := by
    calc
      dist (qubitSpectralBooleanReflection V b) W ≤
          dist (qubitSpectralBooleanReflection V b)
              ((A.contraction gates :
                Matrix.unitaryGroup (Fin n → Bool) ℂ) :
                  Matrix (Fin n → Bool) (Fin n → Bool) ℂ) +
            dist
              ((A.contraction gates :
                Matrix.unitaryGroup (Fin n → Bool) ℂ) :
                  Matrix (Fin n → Bool) (Fin n → Bool) ℂ) W :=
        dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) + 1 / 4 := add_le_add htargetCircuit hCW
      _ = 3 / 4 := by norm_num
  exact (not_lt_of_ge htargetNet) hfar

noncomputable def exactQuarterCircuitNet (n R : ℕ) :
    Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
  if hR : 0 < R then
    Classical.choose
      (exists_exactContinuousTwoQubitCircuit_operatorNet_card_le
        (n := n) (R := R) hR (ε := (1 / 4 : ℝ)) (by norm_num))
  else
    {1}

theorem exactQuarterCircuitNet_cover {n R : ℕ}
    (A : TwoQubitArchitecture n R)
    (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    ∃ W ∈ exactQuarterCircuitNet n R,
      dist
          ((A.contraction gates :
            Matrix.unitaryGroup (Fin n → Bool) ℂ) :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
          (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤ (1 / 4 : ℝ) := by
  classical
  by_cases hR : 0 < R
  · rw [exactQuarterCircuitNet, dif_pos hR]
    exact (Classical.choose_spec
      (exists_exactContinuousTwoQubitCircuit_operatorNet_card_le
        (n := n) (R := R) hR (ε := (1 / 4 : ℝ)) (by norm_num))).1 A gates
  · have hR0 : R = 0 := Nat.eq_zero_of_not_pos hR
    subst R
    refine ⟨1, ?_, ?_⟩
    · simp [exactQuarterCircuitNet]
    · simp [TwoQubitArchitecture.contraction]

theorem exactQuarterCircuitNet_card_real_le (n R : ℕ) :
    ((exactQuarterCircuitNet n R).card : ℝ) ≤
      1 + ((n * n : ℕ) : ℝ) ^ R *
        (1 + 16 * (R : ℝ)) ^ (32 * R) := by
  classical
  by_cases hR : 0 < R
  · have hcard := (Classical.choose_spec
      (exists_exactContinuousTwoQubitCircuit_operatorNet_card_le
        (n := n) (R := R) hR (ε := (1 / 4 : ℝ)) (by norm_num))).2
    have hformula :
        ((exactQuarterCircuitNet n R).card : ℝ) ≤
          ((n * n : ℕ) : ℝ) ^ R *
            (1 + 16 * (R : ℝ)) ^ (32 * R) := by
      rw [exactQuarterCircuitNet, dif_pos hR]
      norm_num [Nat.cast_mul, div_eq_mul_inv] at hcard ⊢
      ring_nf at hcard ⊢
      exact hcard
    linarith
  · have hR0 : R = 0 := Nat.eq_zero_of_not_pos hR
    subst R
    simp [exactQuarterCircuitNet]

noncomputable def atMostQuarterCircuitNet (n s : ℕ) :
    Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
  (Finset.range (s + 1)).biUnion (exactQuarterCircuitNet n)

def atMostQuarterCircuitEntropyBound (n s : ℕ) : ℝ :=
  ∑ R ∈ Finset.range (s + 1),
    (1 + ((n * n : ℕ) : ℝ) ^ R *
      (1 + 16 * (R : ℝ)) ^ (32 * R))

theorem atMostQuarterCircuitNet_card_real_le (n s : ℕ) :
    ((atMostQuarterCircuitNet n s).card : ℝ) ≤
      atMostQuarterCircuitEntropyBound n s := by
  classical
  have hcardNat :
      (atMostQuarterCircuitNet n s).card ≤
        ∑ R ∈ Finset.range (s + 1),
          (exactQuarterCircuitNet n R).card := by
    exact Finset.card_biUnion_le
  have hcardReal :
      ((atMostQuarterCircuitNet n s).card : ℝ) ≤
        ∑ R ∈ Finset.range (s + 1),
          ((exactQuarterCircuitNet n R).card : ℝ) := by
    exact_mod_cast hcardNat
  refine hcardReal.trans ?_
  rw [atMostQuarterCircuitEntropyBound]
  exact Finset.sum_le_sum fun R hR ↦ exactQuarterCircuitNet_card_real_le n R

theorem atMostQuarterCircuitNet_cover
    {n s : ℕ} (C : TwoQubitCircuit n) (hC : C.gateCount ≤ s) :
    ∃ W ∈ atMostQuarterCircuitNet n s,
      dist
          (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
          (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤ (1 / 4 : ℝ) := by
  classical
  obtain ⟨W, hW, hdist⟩ :=
    exactQuarterCircuitNet_cover C.architecture C.gates
  refine ⟨W, ?_, hdist⟩
  rw [atMostQuarterCircuitNet, Finset.mem_biUnion]
  exact ⟨C.gateCount, Finset.mem_range.mpr (by omega), hW⟩

theorem exists_qubitSpectralBooleanReflection_atMostCircuit_fixedError
    {n s : ℕ}
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hEntropy : atMostQuarterCircuitEntropyBound n s <
      ((2 ^ (2 ^ n) : ℕ) : ℝ)) :
    ∃ b : (Fin n → Bool) → Bool,
      ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
        (1 / 2 : ℝ) <
          ‖qubitSpectralBooleanReflection V b -
            (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  classical
  let net := atMostQuarterCircuitNet n s
  have hnetCard' :
      (net.card : ℝ) < ((2 ^ (2 ^ n) : ℕ) : ℝ) :=
    (atMostQuarterCircuitNet_card_real_le n s).trans_lt hEntropy
  have hcard : net.card < 2 ^ (2 ^ n) := by
    exact_mod_cast hnetCard'
  let matrixNet :
      Finset (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
    net.image Subtype.val
  have hmatrixNetCard : matrixNet.card = net.card := by
    exact Finset.card_image_of_injective net Subtype.val_injective
  obtain ⟨b, hb⟩ := exists_bool_far_from_small_net
    (p := qubitSpectralBooleanReflection V)
    (fun hbc => dist_qubitSpectralBooleanReflection_eq_two V hbc)
    matrixNet (by simpa [hmatrixNetCard] using hcard)
  refine ⟨b, ?_⟩
  intro C hC
  obtain ⟨W, hW, hCW⟩ := atMostQuarterCircuitNet_cover C hC
  have hWmatrix :
      (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈ matrixNet := by
    exact Finset.mem_image.mpr ⟨W, hW, rfl⟩
  have hfar := hb W hWmatrix
  by_contra h
  push Not at h
  have htargetCircuit :
      dist (qubitSpectralBooleanReflection V b)
          (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤
        (1 / 2 : ℝ) := by
    simpa [dist_eq_norm] using h
  have htargetNet :
      dist (qubitSpectralBooleanReflection V b)
        (W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤ (3 / 4 : ℝ) := by
    calc
      dist (qubitSpectralBooleanReflection V b) W ≤
          dist (qubitSpectralBooleanReflection V b)
              (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) +
            dist (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) W :=
        dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) + 1 / 4 := add_le_add htargetCircuit hCW
      _ = 3 / 4 := by norm_num
  exact (not_lt_of_ge htargetNet) hfar

private theorem atMostQuarterCircuitEntropyBound_polynomial_majorant
    (q n : ℕ) (hn : 1 ≤ n) :
    atMostQuarterCircuitEntropyBound n (n ^ q) ≤
      (2 : ℝ) ^
        (6 * (64 * (q + 1) * (n + 1) ^ (q + 1)) ^ (2 : ℕ)) := by
  let s : ℕ := n ^ q
  let P : ℕ := 64 * (q + 1) * (n + 1) ^ (q + 1)
  have hs1 : 1 ≤ s := by
    dsimp [s]
    exact Nat.one_le_pow q n (by omega)
  have hsPow : s ≤ (n + 1) ^ (q + 1) := by
    dsimp [s]
    calc
      n ^ q ≤ (n + 1) ^ q := Nat.pow_le_pow_left (by omega) q
      _ ≤ (n + 1) ^ (q + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have h64sP : 64 * s ≤ P := by
    dsimp [P]
    calc
      64 * s ≤ 64 * (n + 1) ^ (q + 1) :=
        Nat.mul_le_mul_left 64 hsPow
      _ ≤ 64 * (q + 1) * (n + 1) ^ (q + 1) := by
        gcongr
        omega
  have hP1 : 1 ≤ P := by omega
  have hsSuccP : s + 1 ≤ P := by omega
  have hnP : n ≤ P := by
    have hnPow : n ≤ (n + 1) ^ (q + 1) := by
      calc
        n ≤ n + 1 := by omega
        _ = (n + 1) ^ (1 : ℕ) := by simp
        _ ≤ (n + 1) ^ (q + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
    dsimp [P]
    calc
      n ≤ (n + 1) ^ (q + 1) := hnPow
      _ ≤ 64 * (q + 1) * (n + 1) ^ (q + 1) := by
        exact Nat.le_mul_of_pos_left _ (by positivity)
  have hPtwo : (P : ℝ) ≤ (2 : ℝ) ^ P := by
    have h := natCast_succ_le_two_pow P
    linarith
  have hbaseN : ((n * n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * P) := by
    have hnPReal : (n : ℝ) ≤ P := by exact_mod_cast hnP
    calc
      ((n * n : ℕ) : ℝ) = (n : ℝ) * n := by norm_num
      _ ≤ (P : ℝ) * P := mul_self_le_mul_self (by positivity) hnPReal
      _ ≤ (2 : ℝ) ^ P * 2 ^ P :=
        mul_le_mul hPtwo hPtwo (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (2 * P) := by rw [← pow_add]; congr 1; omega
  have hbaseR {R : ℕ} (hR : R ≤ s) :
      (1 : ℝ) + 16 * R ≤ (2 : ℝ) ^ (2 * P) := by
    have hnat : 1 + 16 * R ≤ P := by omega
    have hreal : (1 : ℝ) + 16 * R ≤ P := by exact_mod_cast hnat
    calc
      (1 : ℝ) + 16 * R ≤ P := hreal
      _ ≤ (2 : ℝ) ^ P := hPtwo
      _ ≤ (2 : ℝ) ^ (2 * P) := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hterm {R : ℕ} (hR : R ∈ Finset.range (s + 1)) :
      1 + ((n * n : ℕ) : ℝ) ^ R *
          (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
        (2 : ℝ) ^ (4 * P ^ (2 : ℕ) + 1) := by
    have hRle : R ≤ s := by simpa using Finset.mem_range.mp hR
    have hRleP : R ≤ P := hRle.trans (by omega)
    have h32RleP : 32 * R ≤ P := by omega
    have hfirst :
        ((n * n : ℕ) : ℝ) ^ R ≤ (2 : ℝ) ^ (2 * P ^ (2 : ℕ)) := by
      calc
        ((n * n : ℕ) : ℝ) ^ R ≤ ((2 : ℝ) ^ (2 * P)) ^ R :=
          pow_le_pow_left₀ (by positivity) hbaseN R
        _ ≤ ((2 : ℝ) ^ (2 * P)) ^ P :=
          pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hRleP
        _ = (2 : ℝ) ^ (2 * P ^ (2 : ℕ)) := by
          rw [← pow_mul]
          congr 1
          ring
    have hsecond :
        (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
          (2 : ℝ) ^ (2 * P ^ (2 : ℕ)) := by
      calc
        (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
            ((2 : ℝ) ^ (2 * P)) ^ (32 * R) :=
          pow_le_pow_left₀ (by positivity) (hbaseR hRle) (32 * R)
        _ ≤ ((2 : ℝ) ^ (2 * P)) ^ P :=
          pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) h32RleP
        _ = (2 : ℝ) ^ (2 * P ^ (2 : ℕ)) := by
          rw [← pow_mul]
          congr 1
          ring
    have hproduct :
        ((n * n : ℕ) : ℝ) ^ R *
            (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
          (2 : ℝ) ^ (4 * P ^ (2 : ℕ)) := by
      calc
        ((n * n : ℕ) : ℝ) ^ R *
              (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
            (2 : ℝ) ^ (2 * P ^ (2 : ℕ)) * 2 ^ (2 * P ^ (2 : ℕ)) :=
          mul_le_mul hfirst hsecond (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (4 * P ^ (2 : ℕ)) := by
          rw [← pow_add]
          congr 1
          ring
    calc
      1 + ((n * n : ℕ) : ℝ) ^ R *
            (1 + 16 * (R : ℝ)) ^ (32 * R) ≤
          (2 : ℝ) ^ (4 * P ^ (2 : ℕ)) + 2 ^ (4 * P ^ (2 : ℕ)) := by
        exact add_le_add (one_le_pow₀ (by norm_num)) hproduct
      _ = (2 : ℝ) ^ (4 * P ^ (2 : ℕ) + 1) := by
        rw [pow_succ]
        ring
  have hsum :
      atMostQuarterCircuitEntropyBound n s ≤
        ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * P ^ (2 : ℕ) + 1) := by
    rw [atMostQuarterCircuitEntropyBound]
    calc
      ∑ R ∈ Finset.range (s + 1),
          (1 + ((n * n : ℕ) : ℝ) ^ R *
            (1 + 16 * (R : ℝ)) ^ (32 * R)) ≤
          ∑ R ∈ Finset.range (s + 1),
            (2 : ℝ) ^ (4 * P ^ (2 : ℕ) + 1) := by
        exact Finset.sum_le_sum fun R hR ↦ hterm hR
      _ = ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * P ^ (2 : ℕ) + 1) := by
        simp
  have hsPtwo : ((s + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ P := by
    have hsP : ((s + 1 : ℕ) : ℝ) ≤ P := by exact_mod_cast hsSuccP
    exact hsP.trans hPtwo
  calc
    atMostQuarterCircuitEntropyBound n (n ^ q) =
        atMostQuarterCircuitEntropyBound n s := by rfl
    _ ≤ ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * P ^ (2 : ℕ) + 1) := hsum
    _ ≤ (2 : ℝ) ^ P * 2 ^ (4 * P ^ (2 : ℕ) + 1) :=
      mul_le_mul_of_nonneg_right hsPtwo (by positivity)
    _ = (2 : ℝ) ^ (P + (4 * P ^ (2 : ℕ) + 1)) := by rw [← pow_add]
    _ ≤ (2 : ℝ) ^ (6 * P ^ (2 : ℕ)) := by
      exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
    _ = (2 : ℝ) ^
        (6 * (64 * (q + 1) * (n + 1) ^ (q + 1)) ^ (2 : ℕ)) := by rfl

theorem eventually_atMostQuarterCircuitEntropyBound_lt_booleanCarrier
    (q : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      atMostQuarterCircuitEntropyBound n (n ^ q) <
        ((2 ^ (2 ^ n) : ℕ) : ℝ) := by
  let A : ℝ := ((6 * (64 * (q + 1)) ^ (2 : ℕ) : ℕ) : ℝ)
  let E : ℕ := 2 * (q + 1)
  have hlower : ∀ m : ℕ, m ≥ 0 →
      (2 : ℝ) * (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) := by
    intro m hm
    rw [pow_succ]
    simp [mul_comm]
  obtain ⟨N, hN⟩ :=
    GaloisForLFunctions.exists_const_mul_pow_lt_of_geometric_lower
      (b := fun n : ℕ ↦ (2 : ℝ) ^ n)
      (fun _ ↦ by positivity)
      (r := (2 : ℝ)) (by norm_num)
      (N := 0) hlower
      A (by dsimp [A]; positivity) 1 E (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop (max N 1)] with n hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hpoly := hN n hnN
  have hEcast :
      (((6 * (64 * (q + 1) * (n + 1) ^ (q + 1)) ^ (2 : ℕ) : ℕ) : ℝ)) =
        A * (((1 * (n + 1)) ^ E : ℕ) : ℝ) := by
    dsimp [A, E]
    push_cast
    simp only [one_mul]
    rw [show 2 * (q + 1) = (q + 1) * 2 by omega]
    have hpow :
        ((n : ℝ) + 1) ^ ((q + 1) * 2) =
          (((n : ℝ) + 1) ^ (q + 1)) ^ (2 : ℕ) := by
      rw [pow_mul]
    rw [hpow]
    ring
  rw [← hEcast] at hpoly
  have htwoCast : (((2 ^ n : ℕ) : ℝ)) = (2 : ℝ) ^ n := by norm_num
  rw [← htwoCast] at hpoly
  have hExpNat :
      6 * (64 * (q + 1) * (n + 1) ^ (q + 1)) ^ (2 : ℕ) < 2 ^ n := by
    exact_mod_cast hpoly
  calc
    atMostQuarterCircuitEntropyBound n (n ^ q) ≤
        (2 : ℝ) ^
          (6 * (64 * (q + 1) * (n + 1) ^ (q + 1)) ^ (2 : ℕ)) :=
      atMostQuarterCircuitEntropyBound_polynomial_majorant q n hn1
    _ < (2 : ℝ) ^ (2 ^ n) :=
      pow_lt_pow_right₀ (by norm_num) hExpNat
    _ = ((2 ^ (2 ^ n) : ℕ) : ℝ) := by norm_num

/-- Uniform fixed-error hardness against every polynomial-size continuous
two-qubit circuit, on every fixed spectral torus. -/
theorem eventually_exists_qubitSpectralBooleanReflection_polynomialCircuit_fixedError
    (q : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ V : Matrix.unitaryGroup (Fin n → Bool) ℂ,
        ∃ b : (Fin n → Bool) → Bool,
          ∀ C : TwoQubitCircuit n, C.gateCount ≤ n ^ q →
            (1 / 2 : ℝ) <
              ‖qubitSpectralBooleanReflection V b -
                (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  filter_upwards
    [eventually_atMostQuarterCircuitEntropyBound_lt_booleanCarrier q]
      with n hn
  intro V
  exact exists_qubitSpectralBooleanReflection_atMostCircuit_fixedError V hn

/-- Polynomial continuous-circuit entropy is eventually smaller than the
projective Boolean carrier, where one anchor sign has been fixed.  The lost
factor two is exactly the quotient by global sign. -/
theorem eventually_atMostQuarterCircuitEntropyBound_lt_projectiveBooleanCarrier
    (q : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      atMostQuarterCircuitEntropyBound n (n ^ q) <
        ((2 ^ (2 ^ n - 1) : ℕ) : ℝ) := by
  let A : ℝ := ((2 * (6 * (64 * (q + 1)) ^ (2 : ℕ)) : ℕ) : ℝ)
  let E : ℕ := 2 * (q + 1)
  have hlower : ∀ m : ℕ, m ≥ 0 →
      (2 : ℝ) * (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m + 1) := by
    intro m _hm
    rw [pow_succ]
    simp [mul_comm]
  obtain ⟨N, hN⟩ :=
    GaloisForLFunctions.exists_const_mul_pow_lt_of_geometric_lower
      (b := fun n : ℕ ↦ (2 : ℝ) ^ n)
      (fun _ ↦ by positivity)
      (r := (2 : ℝ)) (by norm_num)
      (N := 0) hlower
      A (by dsimp [A]; positivity) 1 E (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop (max N 1)] with n hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hpoly := hN n hnN
  let M : ℕ := 6 * (64 * (q + 1) * (n + 1) ^ (q + 1)) ^ (2 : ℕ)
  have hEcast :
      (((2 * M : ℕ) : ℝ)) =
        A * (((1 * (n + 1)) ^ E : ℕ) : ℝ) := by
    dsimp [A, E, M]
    push_cast
    simp only [one_mul]
    rw [show 2 * (q + 1) = (q + 1) * 2 by omega]
    have hpow :
        ((n : ℝ) + 1) ^ ((q + 1) * 2) =
          (((n : ℝ) + 1) ^ (q + 1)) ^ (2 : ℕ) := by
      rw [pow_mul]
    rw [hpow]
    ring
  rw [← hEcast] at hpoly
  have htwoCast : (((2 ^ n : ℕ) : ℝ)) = (2 : ℝ) ^ n := by norm_num
  rw [← htwoCast] at hpoly
  have hdouble : 2 * M < 2 ^ n := by
    exact_mod_cast hpoly
  have hM : M < 2 ^ n - 1 := by
    have hpow : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn1
    omega
  calc
    atMostQuarterCircuitEntropyBound n (n ^ q) ≤ (2 : ℝ) ^ M := by
      simpa [M] using atMostQuarterCircuitEntropyBound_polynomial_majorant q n hn1
    _ < (2 : ℝ) ^ (2 ^ n - 1) :=
      pow_lt_pow_right₀ (by norm_num) hM
    _ = ((2 ^ (2 ^ n - 1) : ℕ) : ℝ) := by norm_num

end

end GaloisForLFunctions.HTGeometry
