import GaloisForLFunctions.HTGeometry.KreinLangerInertia
import GaloisForLFunctions.HTGeometry.EventualNegDefFromEntrywise
import GaloisForLFunctions.RHTower.VonMangoldtHardyGramScaling
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyNonexpansive

/-!
# Pole-localized exact negative squares

For distinct poles `t_i` in the upper half-plane, this file studies the Pick matrix of the
conjugate-pair carrier

`∑ i, (1 / (z - t_i) + 1 / (z - conj t_i))`.

At the pole-approach nodes `z_j(y) = t_j - i y`, multiplication by `y` produces the limiting
matrix `-2i / (t_j - conj t_l)`.  Its negative is twice a strictly positive Hardy Cauchy Gram
matrix.  Entrywise stability therefore supplies a full `k`-dimensional negative subspace.
Together with the finite-rank upper bound, this proves exactly `k` negative squares after adding
any continuous carrier with positive-semidefinite Pick matrices.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology Filter Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

theorem complex_star_eq_starRingEnd (z : ℂ) :
    star z = (starRingEnd ℂ) z := rfl

theorem complex_posDef_coercive {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x : Fin n → ℂ,
      μ * ‖x‖ ^ (2 : ℕ) ≤ (star x ⬝ᵥ M.mulVec x).re := by
  have hfc : Continuous
      (fun x : Fin n → ℂ => (star x ⬝ᵥ M.mulVec x).re) := by
    fun_prop
  have hhom : ∀ (c : ℝ) (x : Fin n → ℂ),
      (star (c • x) ⬝ᵥ M.mulVec (c • x)).re =
        c ^ (2 : ℕ) * (star x ⬝ᵥ M.mulVec x).re := by
    intro c x
    rw [Matrix.mulVec_smul, star_smul, smul_dotProduct,
      dotProduct_smul]
    simp only [star_trivial, smul_smul]
    change (↑(c * c) *
      (star x ⬝ᵥ M.mulVec x)).re =
        c ^ (2 : ℕ) * (star x ⬝ᵥ M.mulVec x).re
    simp
    ring_nf
    exact Or.inl trivial
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_pos, fun x => by
      rw [Subsingleton.elim x 0]
      simp⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  set S : Set (Fin n → ℂ) := {x | ‖x‖ = 1} with hS
  have hScl : IsClosed S :=
    isClosed_eq continuous_norm continuous_const
  have hSbd : Bornology.IsBounded S := by
    apply (Metric.isBounded_closedBall
      (x := (0 : Fin n → ℂ)) (r := 1)).subset
    intro x hx
    change ‖x‖ = 1 at hx
    simp [Metric.mem_closedBall, dist_zero_right, hx]
  have hScompact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hScl hSbd
  have hSne : S.Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    simp [hS]
  obtain ⟨x₀, hx₀S, hx₀min⟩ :=
    hScompact.exists_isMinOn hSne hfc.continuousOn
  have hx₀ne : x₀ ≠ 0 := by
    intro hx
    rw [hS, Set.mem_setOf_eq, hx, norm_zero] at hx₀S
    norm_num at hx₀S
  set μ : ℝ := (star x₀ ⬝ᵥ M.mulVec x₀).re with hμ
  have hμpos : 0 < μ := by
    exact hM.re_dotProduct_pos hx₀ne
  refine ⟨μ, hμpos, fun x => ?_⟩
  by_cases hx : x = 0
  · subst x
    simp
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : Fin n → ℂ := ‖x‖⁻¹ • x
  have hyS : y ∈ S := by
    change ‖y‖ = 1
    simp [y, norm_smul, hnorm.ne']
  have hmin : μ ≤ (star y ⬝ᵥ M.mulVec y).re :=
    isMinOn_iff.mp hx₀min y hyS
  have hxy : ‖x‖ • y = x := by
    simp [y, smul_smul, hnorm.ne']
  have hQ :
      (star x ⬝ᵥ M.mulVec x).re =
        ‖x‖ ^ (2 : ℕ) * (star y ⬝ᵥ M.mulVec y).re := by
    conv_lhs => rw [← hxy]
    exact hhom ‖x‖ y
  rw [hQ]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hmin (sq_nonneg ‖x‖))

theorem eventually_quadForm_sub_matrix_le
    {n : ℕ} {ι : Type*} {l : Filter ι}
    (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (G₀ : Matrix (Fin n) (Fin n) ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ j k,
      ‖G i j k - G₀ j k‖ ≤ ε) :
    ∀ᶠ i in l, ∀ x : Fin n → ℂ,
      |(star x ⬝ᵥ (G i).mulVec x).re -
          (star x ⬝ᵥ G₀.mulVec x).re|
        ≤ (δ / 2) * ‖x‖ ^ (2 : ℕ) := by
  classical
  set ε : ℝ := δ / (2 * ((n : ℝ) ^ (2 : ℕ) + 1)) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    positivity
  have hεn : ε * (n : ℝ) ^ (2 : ℕ) ≤ δ / 2 := by
    rw [hε, div_mul_eq_mul_div,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ((n : ℝ)), hδ.le]
  filter_upwards [hconv ε hεpos] with i hi
  intro x
  have hsub :
      (star x ⬝ᵥ (G i).mulVec x).re -
          (star x ⬝ᵥ G₀.mulVec x).re =
        (star x ⬝ᵥ (G i - G₀).mulVec x).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
  rw [hsub]
  have hentry : ∀ j k, ‖(G i - G₀) j k‖ ≤ ε := by
    intro j k
    simpa using hi j k
  have hquad :=
    norm_quadForm_le_of_entries (G i - G₀) hεpos.le hentry x
  have hre :
      |(star x ⬝ᵥ (G i - G₀).mulVec x).re| ≤
        ‖star x ⬝ᵥ (G i - G₀).mulVec x‖ :=
    Complex.abs_re_le_norm _
  have hnn : (0 : ℝ) ≤ ‖x‖ ^ (2 : ℕ) := by positivity
  calc
    |(star x ⬝ᵥ (G i - G₀).mulVec x).re| ≤
        ‖star x ⬝ᵥ (G i - G₀).mulVec x‖ := hre
    _ ≤ ε * (n : ℝ) ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) := hquad
    _ ≤ δ / 2 * ‖x‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hεn hnn

theorem eventually_negDef_of_entrywise_tendsto
    {n : ℕ} {ι : Type*} {l : Filter ι}
    (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (G₀ : Matrix (Fin n) (Fin n) ℂ)
    (hneg : (-G₀).PosDef)
    (hconv : ∀ p q,
      Tendsto (fun i => G i p q) l (𝓝 (G₀ p q))) :
    ∀ᶠ i in l, ∀ x : Fin n → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (G i).mulVec x).re < 0 := by
  obtain ⟨δ, hδ, hcoer⟩ := complex_posDef_coercive hneg
  have hconv' : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ p q,
      ‖G i p q - G₀ p q‖ ≤ ε := by
    intro ε hε
    rw [Filter.eventually_all]
    intro p
    rw [Filter.eventually_all]
    intro q
    filter_upwards [Metric.tendsto_nhds.mp
      (hconv p q) ε hε] with i hi
    rw [dist_eq_norm] at hi
    exact hi.le
  have hmod :=
    eventually_quadForm_sub_matrix_le G G₀ hδ hconv'
  apply eventually_neg_of_tendsto_negDef
    (fun i x => (star x ⬝ᵥ (G i).mulVec x).re)
    (fun x => (star x ⬝ᵥ G₀.mulVec x).re)
    (δ := δ)
  · intro x
    have hx := hcoer x
    have hnegQ :
        (star x ⬝ᵥ (-G₀).mulVec x).re =
          -(star x ⬝ᵥ G₀.mulVec x).re := by
      rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
    rw [hnegQ] at hx
    linarith
  · exact hmod
  · exact hδ

/-- Upper-half-plane Hardy Cauchy matrix appearing as the pole-localization limit. -/
def upperPoleLocalizationLimit {k : ℕ} (t : Fin k → ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun i j => (-2 * Complex.I) / (t i - star (t j))

/-- The pole-localization limit is strictly negative definite for distinct upper poles. -/
theorem upperPoleLocalizationLimit_neg_posDef
    {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t) :
    (-upperPoleLocalizationLimit t).PosDef := by
  let w : Fin k → ℂ := fun i => -Complex.I * t i
  have hw : ∀ i, 0 < (w i).re := by
    intro i
    simp [w, Complex.mul_re]
    exact ht i
  have hwinj : Function.Injective w := by
    intro i j hij
    apply htinj
    have h := congrArg (fun z : ℂ => Complex.I * z) hij
    simpa [w] using h
  have hpsd :
      (RHTower.rightHalfPlaneHardyCauchyGram w).PosSemidef :=
    RHTower.rightHalfPlaneHardyCauchyGram_posSemidef hw
  have hdet :
      (RHTower.rightHalfPlaneHardyCauchyGram w).det ≠ 0 := by
    change (RHTower.cauchyRightHalfPlaneGram w).det ≠ 0
    exact RHTower.det_cauchyRightHalfPlaneGram_ne_zero w hw hwinj
  have hpd :
      (RHTower.rightHalfPlaneHardyCauchyGram w).PosDef :=
    hpsd.posDef_iff_det_ne_zero.mpr hdet
  have hscaled :
      ((2 : ℂ) •
        RHTower.rightHalfPlaneHardyCauchyGram w).PosDef :=
    hpd.smul (by norm_num)
  have heq :
      -upperPoleLocalizationLimit t =
        (2 : ℂ) •
          RHTower.rightHalfPlaneHardyCauchyGram w := by
    ext i j
    have hden : t i - star (t j) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith [ht i, ht j]
    simp only [upperPoleLocalizationLimit, Matrix.neg_apply,
      Matrix.smul_apply,
      RHTower.rightHalfPlaneHardyCauchyGram]
    simp [w, star_mul]
    field_simp [hden, Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]
    rw [show -t i + (starRingEnd ℂ) (t j) =
      -(t i - (starRingEnd ℂ) (t j)) by ring, inv_neg]
  rw [heq]
  exact hscaled

/-- Nodes approaching each upper pole vertically from below. -/
def poleApproachNode {k : ℕ}
    (t : Fin k → ℂ) (y : ℝ) (i : Fin k) : ℂ :=
  t i - Complex.I * (y : ℂ)

/-- Pick matrix of an arbitrary scalar carrier. -/
def carrierPickMatrix {N : ℕ}
    (f : ℂ → ℂ) (z : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    (f (z i) - star (f (z j))) / (z i - star (z j))

theorem carrierPickMatrix_add
    {N : ℕ} (f g : ℂ → ℂ) (z : Fin N → ℂ) :
    carrierPickMatrix (fun w => f w + g w) z =
      carrierPickMatrix f z + carrierPickMatrix g z := by
  ext i j
  simp only [carrierPickMatrix, Matrix.of_apply, Matrix.add_apply,
    star_add]
  ring

theorem tendsto_poleApproachNode
    {k : ℕ} (t : Fin k → ℂ) (i : Fin k) :
    Tendsto (fun y : ℝ => poleApproachNode t y i)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (t i)) := by
  have hy : Tendsto (fun y : ℝ => (y : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      inf_le_left
  simpa [poleApproachNode] using
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hy)

theorem tendsto_scaled_multiPairCarrier_poleApproach
    {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t) (j : Fin k) :
    Tendsto
      (fun y : ℝ => (y : ℂ) *
        multiPairCarrier t (poleApproachNode t y j))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (-Complex.I)) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hy : Tendsto (fun y : ℝ => (y : ℂ)) l (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      inf_le_left
  rw [show (fun y : ℝ => (y : ℂ) *
      multiPairCarrier t (poleApproachNode t y j)) =
      fun y : ℝ => ∑ i, (y : ℂ) *
        ((t i - poleApproachNode t y j)⁻¹ +
          (star (t i) - poleApproachNode t y j)⁻¹) by
    funext y
    rw [multiPairCarrier, Finset.mul_sum]]
  have hterm : ∀ i : Fin k,
      Tendsto
        (fun y : ℝ => (y : ℂ) *
          ((t i - poleApproachNode t y j)⁻¹ +
            (star (t i) - poleApproachNode t y j)⁻¹))
        l (𝓝 (if i = j then -Complex.I else 0)) := by
    intro i
    by_cases hij : i = j
    · subst i
      have hsing :
          (fun y : ℝ => (y : ℂ) *
            (t j - poleApproachNode t y j)⁻¹) =ᶠ[l]
          fun _ => -Complex.I := by
        filter_upwards [self_mem_nhdsWithin] with y hypos
        have hyne : (y : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt hypos)
        simp only [poleApproachNode]
        field_simp [hyne, Complex.I_ne_zero]
        ring_nf
        simp [Complex.I_sq]
      have hregDen :
          Tendsto
            (fun y : ℝ =>
              star (t j) - poleApproachNode t y j)
            l (𝓝 (star (t j) - t j)) :=
        tendsto_const_nhds.sub (tendsto_poleApproachNode t j)
      have hregNe : star (t j) - t j ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        simp at him
        linarith [ht j]
      have hreg :
          Tendsto
            (fun y : ℝ =>
              (star (t j) - poleApproachNode t y j)⁻¹)
            l (𝓝 ((star (t j) - t j)⁻¹)) :=
        hregDen.inv₀ hregNe
      have hzero :
          Tendsto
            (fun y : ℝ => (y : ℂ) *
              (star (t j) - poleApproachNode t y j)⁻¹)
            l (𝓝 0) := by
        simpa using hy.mul hreg
      have hsingT :
          Tendsto
            (fun y : ℝ => (y : ℂ) *
              (t j - poleApproachNode t y j)⁻¹)
            l (𝓝 (-Complex.I)) :=
        tendsto_const_nhds.congr' hsing.symm
      simpa [if_pos rfl, mul_add] using hsingT.add hzero
    · have hden₁ :
          Tendsto
            (fun y : ℝ => t i - poleApproachNode t y j)
            l (𝓝 (t i - t j)) :=
        tendsto_const_nhds.sub (tendsto_poleApproachNode t j)
      have hne₁ : t i - t j ≠ 0 :=
        sub_ne_zero.mpr (fun h => hij (htinj h))
      have hinv₁ := hden₁.inv₀ hne₁
      have hden₂ :
          Tendsto
            (fun y : ℝ =>
              star (t i) - poleApproachNode t y j)
            l (𝓝 (star (t i) - t j)) :=
        tendsto_const_nhds.sub (tendsto_poleApproachNode t j)
      have hne₂ : star (t i) - t j ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        simp at him
        linarith [ht i, ht j]
      have hinv₂ := hden₂.inv₀ hne₂
      have hsum := hinv₁.add hinv₂
      simpa [if_neg hij] using hy.mul hsum
  have hsum := tendsto_finsetSum Finset.univ
    (fun i _ => hterm i)
  have hsumLimit :
      (∑ i : Fin k, if i = j then -Complex.I else 0) =
        -Complex.I := by
    rw [Finset.sum_ite_eq' Finset.univ j]
    simp
  simpa [hsumLimit] using hsum

theorem tendsto_scaled_star_multiPairCarrier_poleApproach
    {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t) (j : Fin k) :
    Tendsto
      (fun y : ℝ => (y : ℂ) *
        (starRingEnd ℂ)
          (multiPairCarrier t (poleApproachNode t y j)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 Complex.I) := by
  have hbase :=
    tendsto_scaled_multiPairCarrier_poleApproach t ht htinj j
  have hconj :=
    Complex.continuous_conj.continuousAt.tendsto.comp hbase
  convert hconj using 1
  · funext y
    simp only [Function.comp_apply, map_mul, Complex.conj_ofReal]
  · simp

theorem tendsto_scaled_multiPairPick_poleApproach
    {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t) (i j : Fin k) :
    Tendsto
      (fun y : ℝ => (y : ℂ) *
        multiPairPick t (poleApproachNode t y) i j)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (upperPoleLocalizationLimit t i j)) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hleft :=
    tendsto_scaled_multiPairCarrier_poleApproach t ht htinj i
  have hright :=
    tendsto_scaled_star_multiPairCarrier_poleApproach t ht htinj j
  have hnum : Tendsto
      (fun y : ℝ => (y : ℂ) *
        multiPairCarrier t (poleApproachNode t y i) -
          (y : ℂ) *
            (starRingEnd ℂ)
              (multiPairCarrier t (poleApproachNode t y j)))
      l (𝓝 (-2 * Complex.I)) := by
    have heq : -Complex.I - Complex.I =
        -2 * Complex.I := by ring
    simpa only [heq] using hleft.sub hright
  have hden : Tendsto
      (fun y : ℝ =>
        poleApproachNode t y i -
          star (poleApproachNode t y j))
      l (𝓝 (t i - star (t j))) := by
    exact (tendsto_poleApproachNode t i).sub
      (Complex.continuous_conj.continuousAt.tendsto.comp
        (tendsto_poleApproachNode t j))
  have hdenNe : t i - star (t j) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith [ht i, ht j]
  have hquot := hnum.div hden hdenNe
  have hfun :
      (fun y : ℝ => (y : ℂ) *
        multiPairPick t (poleApproachNode t y) i j) =
      fun y : ℝ =>
        ((y : ℂ) *
            multiPairCarrier t (poleApproachNode t y i) -
          (y : ℂ) * (starRingEnd ℂ)
            (multiPairCarrier t (poleApproachNode t y j))) /
        (poleApproachNode t y i -
          (starRingEnd ℂ) (poleApproachNode t y j)) := by
    funext y
    simp only [multiPairPick, Matrix.of_apply,
      complex_star_eq_starRingEnd]
    ring_nf
  rw [hfun]
  change Tendsto
      (fun y : ℝ =>
        ((y : ℂ) *
            multiPairCarrier t (poleApproachNode t y i) -
          (y : ℂ) * (starRingEnd ℂ)
            (multiPairCarrier t (poleApproachNode t y j))) /
        (poleApproachNode t y i -
          (starRingEnd ℂ) (poleApproachNode t y j)))
      l
      (𝓝 ((-2 * Complex.I) /
        (t i - (starRingEnd ℂ) (t j)))) at hquot
  simpa only [upperPoleLocalizationLimit,
    complex_star_eq_starRingEnd] using hquot

theorem tendsto_scaled_carrierPickMatrix_poleApproach_zero
    {k : ℕ} (B : ℂ → ℂ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (hB : ∀ i, ContinuousAt B (t i))
    (i j : Fin k) :
    Tendsto
      (fun y : ℝ => (y : ℂ) *
        carrierPickMatrix B (poleApproachNode t y) i j)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hy : Tendsto (fun y : ℝ => (y : ℂ)) l (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      inf_le_left
  have hleft :=
    (hB i).tendsto.comp (tendsto_poleApproachNode t i)
  have hright :=
    Complex.continuous_conj.continuousAt.tendsto.comp
      ((hB j).tendsto.comp (tendsto_poleApproachNode t j))
  have hden : Tendsto
      (fun y : ℝ =>
        poleApproachNode t y i -
          star (poleApproachNode t y j))
      l (𝓝 (t i - star (t j))) :=
    (tendsto_poleApproachNode t i).sub
      (Complex.continuous_conj.continuousAt.tendsto.comp
        (tendsto_poleApproachNode t j))
  have hdenNe : t i - star (t j) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith [ht i, ht j]
  have hpick : Tendsto
      (fun y : ℝ =>
        carrierPickMatrix B (poleApproachNode t y) i j)
      l
      (𝓝 ((B (t i) - (starRingEnd ℂ) (B (t j))) /
        (t i - (starRingEnd ℂ) (t j)))) := by
    have hraw := (hleft.sub hright).div hden hdenNe
    have hfun :
        (fun y : ℝ =>
          carrierPickMatrix B (poleApproachNode t y) i j) =
        (fun y : ℝ =>
          (B (poleApproachNode t y i) -
            (starRingEnd ℂ) (B (poleApproachNode t y j))) /
          (poleApproachNode t y i -
            (starRingEnd ℂ) (poleApproachNode t y j))) := by
      rfl
    rw [hfun]
    exact hraw
  simpa using hy.mul hpick

theorem tendsto_scaled_addCarrierPick_poleApproach
    {k : ℕ} (B : ℂ → ℂ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t)
    (hB : ∀ i, ContinuousAt B (t i))
    (i j : Fin k) :
    Tendsto
      (fun y : ℝ => (y : ℂ) *
        carrierPickMatrix
          (fun z => B z + multiPairCarrier t z)
          (poleApproachNode t y) i j)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (upperPoleLocalizationLimit t i j)) := by
  have hBzero :=
    tendsto_scaled_carrierPickMatrix_poleApproach_zero
      B t ht hB i j
  have hpair :=
    tendsto_scaled_multiPairPick_poleApproach
      t ht htinj i j
  have hadd := hBzero.add hpair
  have hfun :
      (fun y : ℝ => (y : ℂ) *
        carrierPickMatrix
          (fun z => B z + multiPairCarrier t z)
          (poleApproachNode t y) i j) =
      fun y : ℝ =>
        (y : ℂ) *
          carrierPickMatrix B (poleApproachNode t y) i j +
        (y : ℂ) *
          multiPairPick t (poleApproachNode t y) i j := by
    funext y
    simp only [carrierPickMatrix, multiPairPick, Matrix.of_apply,
      star_add]
    ring
  rw [hfun]
  simpa only [zero_add] using hadd

theorem eventually_poleApproachNode_upper
    {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im) :
    ∀ᶠ y : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ i, 0 < (poleApproachNode t y i).im := by
  rw [Filter.eventually_all]
  intro i
  have hy : Tendsto (fun y : ℝ => y)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  filter_upwards [hy.eventually_lt_const (ht i)] with y hylt
  simp [poleApproachNode]
  linarith

theorem eventually_poleApproachNode_avoids_poles
    {k : ℕ} (t : Fin k → ℂ)
    (htinj : Function.Injective t) :
    ∀ᶠ y : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ i j, poleApproachNode t y j ≠ t i := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  by_cases hij : i = j
  · subst i
    filter_upwards [self_mem_nhdsWithin] with y hy
    intro h
    have him := congrArg Complex.im h
    simp [poleApproachNode] at him
    have hypos : 0 < y := hy
    linarith
  · exact (tendsto_poleApproachNode t j).eventually_ne
      (Ne.symm (fun h => hij (htinj h)))

/-- After pole-localization scaling, a continuous background plus the pair carrier is eventually
negative definite on the full `k`-dimensional node space. -/
theorem eventually_negDef_add_multiPairCarrier_poleApproach
    {k : ℕ} (B : ℂ → ℂ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t)
    (hB : ∀ i, ContinuousAt B (t i)) :
    ∀ᶠ y : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ x : Fin k → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
          (carrierPickMatrix
            (fun z => B z + multiPairCarrier t z)
            (poleApproachNode t y)).mulVec x).re < 0 := by
  let G : ℝ → Matrix (Fin k) (Fin k) ℂ := fun y =>
    (y : ℂ) •
      carrierPickMatrix
        (fun z => B z + multiPairCarrier t z)
        (poleApproachNode t y)
  have hconv : ∀ i j,
      Tendsto (fun y => G y i j)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (upperPoleLocalizationLimit t i j)) := by
    intro i j
    simpa only [G, Matrix.smul_apply, smul_eq_mul] using
      tendsto_scaled_addCarrierPick_poleApproach
        B t ht htinj hB i j
  have hscaled :=
    eventually_negDef_of_entrywise_tendsto
      G (upperPoleLocalizationLimit t)
      (upperPoleLocalizationLimit_neg_posDef t ht htinj)
      hconv
  filter_upwards [hscaled, self_mem_nhdsWithin] with y hyneg hypos
  intro x hx
  have hs := hyneg x hx
  have hyreal : ((y : ℂ).re) = y := by simp
  have hyimag : ((y : ℂ).im) = 0 := by simp
  change (star x ⬝ᵥ
      (((y : ℂ) •
        carrierPickMatrix
          (fun z => B z + multiPairCarrier t z)
          (poleApproachNode t y)).mulVec x)).re < 0 at hs
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, hyreal, hyimag, zero_mul, sub_zero] at hs
  have hypos' : 0 < y := hypos
  nlinarith

/-- Pole-localized nodes witnessing the full `k` negative directions exist inside the upper
half-plane and avoid every pole. -/
theorem exists_poleApproachNode_negDef_add_multiPairCarrier
    {k : ℕ} (B : ℂ → ℂ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t)
    (hB : ∀ i, ContinuousAt B (t i)) :
    ∃ y : ℝ, 0 < y ∧
      (∀ i, 0 < (poleApproachNode t y i).im) ∧
      (∀ i j, poleApproachNode t y j ≠ t i) ∧
      Function.Injective (poleApproachNode t y) ∧
      ∀ x : Fin k → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
          (carrierPickMatrix
            (fun z => B z + multiPairCarrier t z)
            (poleApproachNode t y)).mulVec x).re < 0 := by
  have hneg :=
    eventually_negDef_add_multiPairCarrier_poleApproach
      B t ht htinj hB
  have hupper := eventually_poleApproachNode_upper t ht
  have havoid :=
    eventually_poleApproachNode_avoids_poles t htinj
  have hall : ∀ᶠ y : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < y ∧
      (∀ i, 0 < (poleApproachNode t y i).im) ∧
      (∀ i j, poleApproachNode t y j ≠ t i) ∧
      (∀ x : Fin k → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
          (carrierPickMatrix
            (fun z => B z + multiPairCarrier t z)
            (poleApproachNode t y)).mulVec x).re < 0) := by
    filter_upwards [self_mem_nhdsWithin, hupper, havoid, hneg]
      with y hy hu ha hn
    exact ⟨hy, hu, ha, hn⟩
  obtain ⟨y, hy, hu, ha, hn⟩ := hall.exists
  refine ⟨y, hy, hu, ha, ?_, hn⟩
  intro i j hij
  apply htinj
  have h := congrArg
    (fun z : ℂ => z + Complex.I * (y : ℂ)) hij
  simpa [poleApproachNode] using h

/-- Adding a positive-semidefinite Pick background cannot create more negative directions. -/
theorem neg_inertia_le_add_posSemidef
    {N k : ℕ}
    (H P : Matrix (Fin N) (Fin N) ℂ)
    (hP : P.PosSemidef)
    (hH : ∀ W : Submodule ℂ (Fin N → ℂ),
      (∀ x ∈ W, x ≠ 0 →
        (star x ⬝ᵥ H.mulVec x).re < 0) →
      Module.finrank ℂ W ≤ k)
    (W : Submodule ℂ (Fin N → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 →
      (star x ⬝ᵥ (P + H).mulVec x).re < 0) :
    Module.finrank ℂ W ≤ k := by
  apply hH W
  intro x hx hx0
  have htotal := hW x hx hx0
  have hnonneg := hP.re_dotProduct_nonneg x
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re] at htotal
  by_contra hnot
  have hHnonneg :
      0 ≤ (star x ⬝ᵥ H.mulVec x).re := le_of_not_gt hnot
  exact (not_lt_of_ge (add_nonneg hnonneg hHnonneg)) htotal

/-- **Exact negative-square theorem with a positive background.**  A continuous carrier whose Pick
matrices are positive semidefinite may be added to `k` distinct upper conjugate-pair poles.  Every
finite Pick matrix then has negative inertia at most `k`, while a pole-localized `k`-node matrix is
negative definite on the full coordinate space. -/
theorem add_multiPairCarrier_exact_negativeSquares
    {k : ℕ} (B : ℂ → ℂ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t)
    (hBcont : ∀ i, ContinuousAt B (t i))
    (hBpsd : ∀ {N : ℕ} (z : Fin N → ℂ),
      (∀ j, 0 < (z j).im) →
      (carrierPickMatrix B z).PosSemidef) :
    (∀ {N : ℕ} (z : Fin N → ℂ),
      (∀ j, 0 < (z j).im) →
      (∀ i j, z j ≠ t i) →
      ∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ x ∈ W, x ≠ 0 →
          (star x ⬝ᵥ
            (carrierPickMatrix
              (fun w => B w + multiPairCarrier t w) z).mulVec x).re < 0) →
        Module.finrank ℂ W ≤ k) ∧
      ∃ z : Fin k → ℂ,
        (∀ j, 0 < (z j).im) ∧
        (∀ i j, z j ≠ t i) ∧
        Function.Injective z ∧
        ∀ x : Fin k → ℂ, x ≠ 0 →
          (star x ⬝ᵥ
            (carrierPickMatrix
              (fun w => B w + multiPairCarrier t w) z).mulVec x).re < 0 := by
  constructor
  · intro N z hz hzt W hW
    have hpair :
        ∀ V : Submodule ℂ (Fin N → ℂ),
          (∀ x ∈ V, x ≠ 0 →
            (star x ⬝ᵥ (multiPairPick t z).mulVec x).re < 0) →
          Module.finrank ℂ V ≤ k :=
      fun V hV =>
        multi_pair_pick_neg_inertia_le t z ht hz
          hzt V hV
    have htotal :
        carrierPickMatrix
            (fun w => B w + multiPairCarrier t w) z =
          carrierPickMatrix B z + multiPairPick t z := by
      rw [carrierPickMatrix_add]
      rfl
    rw [htotal] at hW
    exact neg_inertia_le_add_posSemidef
      (multiPairPick t z) (carrierPickMatrix B z)
      (hBpsd z hz) hpair W hW
  · obtain ⟨y, hy, hu, ha, hinj, hneg⟩ :=
      exists_poleApproachNode_negDef_add_multiPairCarrier
        B t ht htinj hBcont
    exact ⟨poleApproachNode t y, hu, ha, hinj, hneg⟩

end

end GaloisForLFunctions.HTGeometry
