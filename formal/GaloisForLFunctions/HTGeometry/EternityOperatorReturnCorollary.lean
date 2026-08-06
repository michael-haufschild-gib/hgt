import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.ProjectiveExactReturnRankOne
import GaloisForLFunctions.HTGeometry.EternityEigenvaluePresentation

/-!
# Exact projective repetition in operator norm

Exact global projective return is stated arithmetically, as the existence of a positive time
placing every spectral gap in `2πℤ`.  Its operator meaning is that the evolution returns to a
scalar multiple of the identity.  This file proves the two are the same condition, and therefore
that a simple spectrum repeats exactly in operator norm precisely when its gap rank is one.
-/

open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A unit-circle character equals one exactly at integer representatives. -/
theorem fourier_one_coe_eq_one_iff (y : ℝ) :
    fourier 1 ((y : ℝ) : UnitAddCircle) = 1 ↔ ∃ m : ℤ, y = (m : ℝ) := by
  rw [fourier_coe_apply]
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (y : ℂ) / ((1 : ℝ) : ℂ)
      = (y : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by exact_mod_cast mul_right_cancel₀ hne hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The degenerate chord target is the exact arithmetic return condition. -/
theorem mem_anchoredProjectiveReturnTarget_zero_iff (E : d → ℝ) (a : d) (t : ℝ) :
    finiteClockPhasePoint (projectiveFrequency E a) t ∈ anchoredProjectiveReturnTarget 0
      ↔ ∀ i : {i : d // i ≠ a}, ∃ m : ℤ, t * (E i - E a) = 2 * Real.pi * (m : ℝ) := by
  have hpi : (2 * Real.pi) ≠ 0 := by
    have := Real.pi_ne_zero
    intro hcon
    apply this
    linarith [hcon]
  constructor
  · intro hmem i
    have h := hmem i
    have hzero : ‖fourier 1 (finiteClockPhasePoint (projectiveFrequency E a) t i) - 1‖ = 0 :=
      le_antisymm h (norm_nonneg _)
    have hone : fourier 1 (finiteClockPhasePoint (projectiveFrequency E a) t i) = 1 :=
      sub_eq_zero.mp (norm_eq_zero.mp hzero)
    have hpoint : finiteClockPhasePoint (projectiveFrequency E a) t i
        = ((t * (E i - E a) / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
    rw [hpoint, fourier_one_coe_eq_one_iff] at hone
    obtain ⟨m, hm⟩ := hone
    refine ⟨m, ?_⟩
    field_simp at hm
    linarith [hm]
  · intro hall i
    obtain ⟨m, hm⟩ := hall i
    have hpoint : finiteClockPhasePoint (projectiveFrequency E a) t i
        = ((t * (E i - E a) / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
    have hone : fourier 1 (finiteClockPhasePoint (projectiveFrequency E a) t i) = 1 := by
      rw [hpoint, fourier_one_coe_eq_one_iff]
      exact ⟨m, by rw [hm]; field_simp⟩
    show ‖fourier 1 (finiteClockPhasePoint (projectiveFrequency E a) t i) - 1‖ ≤ 0
    rw [hone, sub_self, norm_zero]

variable {n : ℕ}

/-- **Exact projective repetition in operator norm.**  A Hermitian generator returns to a scalar
multiple of the identity at some positive time exactly when it has a positive exact global
projective return. -/
theorem exists_pos_unitaryEvolution_eq_anchorPhase_smul_one_iff
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian) :
    (∃ t : ℝ, 0 < t ∧ unitaryEvolution H t
        = anchorPhase hH.eigenvalues 0 t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      ↔ HasPositiveProjectiveReturn hH.eigenvalues := by
  constructor
  · rintro ⟨t, ht, hteq⟩
    refine ⟨t, ht, fun j => ?_⟩
    have h := (unitaryEvolution_eq_anchorPhase_smul_one_iff hH 0 t).mp hteq
    rw [mem_anchoredProjectiveReturnTarget_zero_iff] at h
    exact h ⟨j.succ, Fin.succ_ne_zero j⟩
  · rintro ⟨t, ht, hall⟩
    refine ⟨t, ht, ?_⟩
    rw [unitaryEvolution_eq_anchorPhase_smul_one_iff hH 0 t,
      mem_anchoredProjectiveReturnTarget_zero_iff]
    rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
    exact hall j

/-- **Corollary 1 in operator form.**  A Hermitian matrix with simple spectrum repeats exactly in
operator norm, up to a global phase, exactly when its gap rank is one. -/
theorem exists_pos_unitaryEvolution_eq_anchorPhase_smul_one_iff_gapRank_eq_one (hn : 0 < n)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian)
    (hinj : Function.Injective hH.eigenvalues) :
    (∃ t : ℝ, 0 < t ∧ unitaryEvolution H t
        = anchorPhase hH.eigenvalues 0 t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      ↔ rationalCoordinateRank (fun j : Fin n => hH.eigenvalues j.succ - hH.eigenvalues 0) = 1 := by
  rw [exists_pos_unitaryEvolution_eq_anchorPhase_smul_one_iff hH,
    hasPositiveProjectiveReturn_iff_gapRank_eq_one hn hinj]

/-- **Corollary 1 in operator form, with a horizon fixed in advance.**  From three levels onward,
every uniform bounded-horizon tube around every Hermitian matrix contains a commuting neighbour with
simple spectrum whose evolution reaches a scalar multiple of the identity at some positive time, and
another whose evolution never does — while both stay within `η` of the original evolution for every
time of modulus at most `T`. -/
theorem exists_isHermitian_commuting_operatorPeriodic_and_aperiodic_uniform_horizon
    (hn : 2 ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    (∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian),
        B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
          (∃ t : ℝ, 0 < t ∧ unitaryEvolution B t
            = anchorPhase hB.eigenvalues 0 t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ∧
          ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
      ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian),
        B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
          (¬ ∃ t : ℝ, 0 < t ∧ unitaryEvolution B t
            = anchorPhase hB.eigenvalues 0 t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ∧
          ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η := by
  obtain ⟨⟨B₁, hB₁, hcomm₁, hinj₁, hret₁, hclose₁⟩, ⟨B₂, hB₂, hcomm₂, hinj₂, hret₂, hclose₂⟩⟩ :=
    exists_isHermitian_commuting_eigenvaluePeriodic_and_aperiodic_uniform_horizon hn A hA hT hη
  refine ⟨⟨B₁, hB₁, hcomm₁, hinj₁, ?_, hclose₁⟩, ⟨B₂, hB₂, hcomm₂, hinj₂, ?_, hclose₂⟩⟩
  · exact (exists_pos_unitaryEvolution_eq_anchorPhase_smul_one_iff hB₁).mpr hret₁
  · intro hcon
    exact hret₂ ((exists_pos_unitaryEvolution_eq_anchorPhase_smul_one_iff hB₂).mp hcon)

/-! ### The perturbation distance is the spectral shift -/

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- **Theorem B's displayed norm identity.**  Transporting a prescribed spectrum back through the
eigenbasis moves the matrix by exactly the supremum of the spectral shifts:

```text
‖H - K‖ = max_j |λ_j - λ'_j| .
```
-/
theorem l2_opNorm_spectralTransport_sub {H : Matrix d d ℂ} (hH : H.IsHermitian) (E' : d → ℝ) :
    ‖(hH.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i => (E' i : ℂ))
        * star (hH.eigenvectorUnitary : Matrix d d ℂ) - H‖
      = ‖fun i : d => E' i - hH.eigenvalues i‖ := by
  set V : Matrix d d ℂ := (hH.eigenvectorUnitary : Matrix d d ℂ) with hVdef
  have hV : V ∈ unitary (Matrix d d ℂ) := hH.eigenvectorUnitary.2
  have hdiff : V * Matrix.diagonal (fun i => (E' i : ℂ)) * star V - H
      = V * Matrix.diagonal (fun i => ((E' i : ℂ) - (hH.eigenvalues i : ℂ))) * star V := by
    conv_lhs => rw [isHermitian_eq_conj_diagonal hH]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]
  rw [hdiff, l2_opNorm_unitary_conj_eq hV, Matrix.l2_opNorm_diagonal]
  simp only [Pi.norm_def]
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  refine NNReal.coe_injective ?_
  simp only [coe_nnnorm]
  rw [show ((E' i : ℂ) - (hH.eigenvalues i : ℂ)) = (((E' i - hH.eigenvalues i : ℝ)) : ℂ) by
    push_cast; ring, Complex.norm_real]

/-- The same identity in the conjugation form the perturbation theorem produces. -/
theorem l2_opNorm_conjStarAlgAut_diagonal_sub {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (E' : d → ℝ) :
    ‖(Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) hH.eigenvectorUnitary)
        (Matrix.diagonal (RCLike.ofReal ∘ E')) - H‖
      = ‖fun i : d => E' i - hH.eigenvalues i‖ := by
  rw [Unitary.conjStarAlgAut_apply]
  exact l2_opNorm_spectralTransport_sub hH E'

/-- **Theorem C's mechanism, exactly.**  Two spectra transported through one eigenbasis generate
evolutions whose operator distance is exactly the largest phase chord:

```text
‖e^{-itK} - e^{-itH}‖ = max_j |e^{-itλ'_j} - e^{-itλ_j}| .
```

The card's bound `(1)` is this identity together with the scalar Lipschitz estimate on each
chord. -/
theorem l2_opNorm_unitaryEvolution_spectralTransport_sub {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (E' : d → ℝ) (t : ℝ) :
    ‖unitaryEvolution ((hH.eigenvectorUnitary : Matrix d d ℂ)
          * Matrix.diagonal (fun i => (E' i : ℂ))
          * star (hH.eigenvectorUnitary : Matrix d d ℂ)) t - unitaryEvolution H t‖
      = ‖fun i : d => Complex.exp (-(Complex.I * (t * E' i)))
          - Complex.exp (-(Complex.I * (t * hH.eigenvalues i)))‖ := by
  have hsub : (Matrix.diagonal fun i : d => Complex.exp (-(Complex.I * ((t : ℂ) * (E' i : ℂ)))))
        - (Matrix.diagonal fun i : d =>
            Complex.exp (-(Complex.I * ((t : ℂ) * (hH.eigenvalues i : ℂ)))))
      = Matrix.diagonal (fun i : d => Complex.exp (-(Complex.I * ((t : ℂ) * (E' i : ℂ))))
          - Complex.exp (-(Complex.I * ((t : ℂ) * (hH.eigenvalues i : ℂ))))) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h]
  rw [unitaryEvolution_conj_diagonal _ hH.eigenvectorUnitary.2, unitaryEvolution_spectral hH,
    ← Matrix.sub_mul, ← Matrix.mul_sub, hsub,
    l2_opNorm_unitary_conj_eq hH.eigenvectorUnitary.2, Matrix.l2_opNorm_diagonal]

/-- The chord between two phases of the same real argument. -/
theorem norm_exp_neg_I_mul_sub_exp_neg_I_mul (t a b : ℝ) :
    ‖Complex.exp (-(Complex.I * ((t : ℂ) * (a : ℂ))))
        - Complex.exp (-(Complex.I * ((t : ℂ) * (b : ℂ))))‖
      = ‖2 * Real.sin (t * (a - b) / 2)‖ := by
  have hfactor : Complex.exp (-(Complex.I * ((t : ℂ) * (a : ℂ))))
        - Complex.exp (-(Complex.I * ((t : ℂ) * (b : ℂ))))
      = Complex.exp (-(Complex.I * ((t : ℂ) * (b : ℂ))))
        * (Complex.exp (-(Complex.I * ((t * (a - b) : ℝ) : ℂ))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hunit : ‖Complex.exp (-(Complex.I * ((t : ℂ) * (b : ℂ))))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * ((t : ℂ) * (b : ℂ)))).re = 0 := by simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  rw [hfactor, norm_mul, hunit, one_mul,
    norm_exp_neg_I_mul_sub_one (t * (a - b)), Complex.norm_exp_I_mul_ofReal_sub_one]

/-- **Theorem C's distance in closed form.**  The evolution distance of two spectra transported
through one eigenbasis is twice the largest sine of half the spectral shift. -/
theorem l2_opNorm_unitaryEvolution_spectralTransport_sub_eq_sin {H : Matrix d d ℂ}
    (hH : H.IsHermitian) (E' : d → ℝ) (t : ℝ) :
    ‖unitaryEvolution ((hH.eigenvectorUnitary : Matrix d d ℂ)
          * Matrix.diagonal (fun i => (E' i : ℂ))
          * star (hH.eigenvectorUnitary : Matrix d d ℂ)) t - unitaryEvolution H t‖
      = ‖fun i : d => 2 * Real.sin (t * (E' i - hH.eigenvalues i) / 2)‖ := by
  rw [l2_opNorm_unitaryEvolution_spectralTransport_sub hH E' t]
  simp only [Pi.norm_def]
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  refine NNReal.coe_injective ?_
  simp only [coe_nnnorm]
  exact norm_exp_neg_I_mul_sub_exp_neg_I_mul t (E' i) (hH.eigenvalues i)

/-- **Theorem C `(1)` by the card's route.**  Comparing the closed-form evolution distance with the
spectral-shift norm through `|sin x| ≤ |x|` gives the Lipschitz bound directly, with `‖K - H‖` the
exact spectral shift of Theorem B. -/
theorem l2_opNorm_unitaryEvolution_spectralTransport_sub_le {H : Matrix d d ℂ}
    (hH : H.IsHermitian) (E' : d → ℝ) (t : ℝ) :
    ‖unitaryEvolution ((hH.eigenvectorUnitary : Matrix d d ℂ)
          * Matrix.diagonal (fun i => (E' i : ℂ))
          * star (hH.eigenvectorUnitary : Matrix d d ℂ)) t - unitaryEvolution H t‖
      ≤ |t| * ‖(hH.eigenvectorUnitary : Matrix d d ℂ)
          * Matrix.diagonal (fun i => (E' i : ℂ))
          * star (hH.eigenvectorUnitary : Matrix d d ℂ) - H‖ := by
  rw [l2_opNorm_unitaryEvolution_spectralTransport_sub_eq_sin hH E' t,
    l2_opNorm_spectralTransport_sub hH E']
  have hnonneg : 0 ≤ |t| * ‖fun i : d => E' i - hH.eigenvalues i‖ :=
    mul_nonneg (abs_nonneg t) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hnonneg).mpr fun i => ?_
  have hchord : ‖2 * Real.sin (t * (E' i - hH.eigenvalues i) / 2)‖
      ≤ |t| * |E' i - hH.eigenvalues i| := by
    have hsin := Real.abs_sin_le_abs (x := t * (E' i - hH.eigenvalues i) / 2)
    have habs : |t * (E' i - hH.eigenvalues i) / 2| = |t| * |E' i - hH.eigenvalues i| / 2 := by
      rw [abs_div, abs_mul]
      norm_num
    rw [Real.norm_eq_abs, abs_mul]
    rw [habs] at hsin
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    linarith
  refine le_trans hchord ?_
  exact mul_le_mul_of_nonneg_left
    (by simpa using norm_le_pi_norm (fun i : d => E' i - hH.eigenvalues i) i) (abs_nonneg t)

/-! ### The public theorem -/

/-- **The card's public theorem, on the operator.**  From three levels onward, fix any Hermitian
generator, any horizon and any tolerance.  Then

* every temporal dimension `1, …, D-1` is realized by a commuting neighbour with simple spectrum
  whose evolution stays within the tolerance over the whole horizon, and
* among those neighbours there is one whose evolution reaches a scalar multiple of the identity at
  some positive time and one whose evolution never does.

So every possible dimension of infinite-time recurrence, and both exact repetition and exact
nonrepetition, occur arbitrarily close to every Hamiltonian, indistinguishably on any horizon fixed
in advance. -/
theorem eternity_public_theorem (hn : 2 ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : A.IsHermitian) {T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    (∀ k : ℕ, 0 < k → k ≤ n →
        ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian),
          B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
            rationalCoordinateRank
                (fun j : Fin n => hB.eigenvalues j.succ - hB.eigenvalues 0) = k ∧
            ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η)
      ∧ (∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian),
          B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
            (∃ t : ℝ, 0 < t ∧ unitaryEvolution B t
              = anchorPhase hB.eigenvalues 0 t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ∧
            ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η)
      ∧ (∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian),
          B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
            (¬ ∃ t : ℝ, 0 < t ∧ unitaryEvolution B t
              = anchorPhase hB.eigenvalues 0 t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ∧
            ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) := by
  obtain ⟨hper, haper⟩ :=
    exists_isHermitian_commuting_operatorPeriodic_and_aperiodic_uniform_horizon hn A hA hT hη
  exact ⟨fun k hk hkn =>
    exists_isHermitian_commuting_eigenvalueGapRank_uniform_horizon hk hkn A hA hT hη,
    hper, haper⟩

end

end GaloisForLFunctions.HTGeometry
