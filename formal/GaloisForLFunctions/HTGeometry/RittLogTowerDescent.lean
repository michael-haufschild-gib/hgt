import GaloisForLFunctions.HTGeometry.RittLogTowerConnection

/-!
# The weight descent of a tower relation

A relation `towerShift F = ρ^J·F + G` in the polynomial ring of the jets is compared layer by
layer.  At the top layer of the filtration the comparison is the base relation

`ψ(F_d) = ρ^{J+W}·F_d + ρ^W·G_d`,

so a nonzero top coefficient is an obstruction as soon as the exponent `J + W` is nontrivial: an
affine transport equation when `G_d ≠ 0`, and Ritt's order-one form when it vanishes.  If the whole
top layer of `F` vanishes then so does that of `G`, and the same comparison applies one layer down.

Consequently a relation all of whose exponents `J + k` are nontrivial forces `F = 0` and `G = 0`,
unless an obstruction exists.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

open MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- The two base obstructions of the affine tower. -/
def TowerObstruction (Fr : RittFrame K L) : Prop :=
  (∃ (w : K) (I : ℤ), w ≠ 0 ∧ I ≠ 0 ∧ Fr.ψ w = Fr.ρ ^ I * w) ∨
  (∃ (w h : K) (I : ℤ), w ≠ 0 ∧ h ≠ 0 ∧ Fr.ψ w = Fr.ρ ^ I * w + h)

theorem weight_eq_zero_iff {e : Fin n →₀ ℕ} :
    Finsupp.weight (jetWeight n) e = 0 ↔ e = 0 := by
  classical
  constructor
  · intro h
    rw [weight_eq_sum e] at h
    ext j
    by_cases hj : j ∈ e.support
    · have hz := Finset.sum_eq_zero_iff.mp h j hj
      simp only [jetWeight] at hz
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      exact (Nat.mul_eq_zero.mp hz).resolve_right (by omega)
    · simpa using Finsupp.notMem_support_iff.mp hj
  · rintro rfl
    simp

theorem eq_zero_of_wLe_zero {F : MvPolynomial (Fin n) K} (hF : WLe n F 0)
    (h0 : coeff 0 F = 0) : F = 0 := by
  classical
  ext e
  rw [coeff_zero]
  by_contra hne
  have hmem : e ∈ F.support := MvPolynomial.mem_support_iff.mpr hne
  have hw : Finsupp.weight (jetWeight n) e = 0 := Nat.le_zero.mp (hF e hmem)
  rw [weight_eq_zero_iff.mp hw] at hne
  exact hne h0

theorem wLe_of_top_vanishing {F : MvPolynomial (Fin n) K} {W : ℕ} (hF : WLe n F (W + 1))
    (htop : ∀ d : Fin n →₀ ℕ, Finsupp.weight (jetWeight n) d = W + 1 → coeff d F = 0) :
    WLe n F W := by
  intro e he
  have h1 := hF e he
  rcases Nat.lt_or_ge (Finsupp.weight (jetWeight n) e) (W + 1) with h | h
  · omega
  · have heq : Finsupp.weight (jetWeight n) e = W + 1 := by omega
    exact absurd (htop e heq) (MvPolynomial.mem_support_iff.mp he)

/-- **The weight descent.**  A tower relation whose exponents are all nontrivial has only the
trivial solution, unless a base obstruction exists. -/
theorem obstruction_or_zero_of_towerRelation (Fr : RittFrame K L) (b : K) {J : ℤ} :
    ∀ (W : ℕ) (F G : MvPolynomial (Fin n) K), WLe n F W → WLe n G W →
      (∀ k : ℕ, k ≤ W → J + (k : ℤ) ≠ 0) →
      Fr.towerShift b n F = C (Fr.ρ ^ J) * F + G →
      TowerObstruction Fr ∨ (F = 0 ∧ G = 0) := by
  classical
  intro W
  induction W with
  | zero =>
      intro F G hF hG hJ hrel
      have hd : Finsupp.weight (jetWeight n) (0 : Fin n →₀ ℕ) = 0 := by simp
      have h := Fr.base_relation_of_towerShift b hF hrel hd
      simp only [pow_zero, mul_one, one_mul] at h
      by_cases hF0 : coeff 0 F = 0
      · have hFz : F = 0 := eq_zero_of_wLe_zero hF hF0
        rw [hF0, map_zero, mul_zero, zero_add] at h
        have hG0 : coeff 0 G = 0 := by
          simpa using h.symm
        exact Or.inr ⟨hFz, eq_zero_of_wLe_zero hG hG0⟩
      · refine Or.inl ?_
        by_cases hG0 : coeff 0 G = 0
        · rw [hG0, add_zero] at h
          exact Or.inl ⟨coeff 0 F, J, hF0, by simpa using hJ 0 (le_refl 0), h⟩
        · exact Or.inr ⟨coeff 0 F, coeff 0 G, J, hF0, hG0, by simpa using h⟩
  | succ W ih =>
      intro F G hF hG hJ hrel
      by_cases htop : ∀ d : Fin n →₀ ℕ, Finsupp.weight (jetWeight n) d = W + 1 → coeff d F = 0
      · have hFW : WLe n F W := wLe_of_top_vanishing hF htop
        have hGtop : ∀ d : Fin n →₀ ℕ, Finsupp.weight (jetWeight n) d = W + 1 →
            coeff d G = 0 := by
          intro d hd
          have h := Fr.base_relation_of_towerShift b hF hrel hd
          rw [htop d hd, map_zero, mul_zero, zero_add] at h
          have hpow : (Fr.ρ : K) ^ (W + 1) ≠ 0 := pow_ne_zero _ Fr.ρ_ne
          exact (mul_eq_zero.mp h.symm).resolve_left hpow
        exact ih F G hFW (wLe_of_top_vanishing hG hGtop)
          (fun k hk => hJ k (by omega)) hrel
      · push Not at htop
        obtain ⟨d, hd, hFd⟩ := htop
        have h := Fr.base_relation_of_towerShift b hF hrel hd
        refine Or.inl ?_
        by_cases hGd : (Fr.ρ : K) ^ (W + 1) * coeff d G = 0
        · rw [hGd, add_zero] at h
          refine Or.inl ⟨coeff d F, J + ((W + 1 : ℕ) : ℤ), hFd, hJ (W + 1) (le_refl _), ?_⟩
          rw [h, zpow_add₀ Fr.ρ_ne, zpow_natCast]
        · exact Or.inr ⟨coeff d F, (Fr.ρ : K) ^ (W + 1) * coeff d G,
            J + ((W + 1 : ℕ) : ℤ), hFd, hGd, by
              rw [h, zpow_add₀ Fr.ρ_ne, zpow_natCast]⟩

/-- **The weight descent down to a floor.** -/
theorem obstruction_or_wLe_of_towerRelation (Fr : RittFrame K L) (b : K) {J : ℤ} (W₀ : ℕ) :
    ∀ (m : ℕ) (F G : MvPolynomial (Fin n) K), WLe n F (W₀ + m) → WLe n G (W₀ + m) →
      (∀ k : ℕ, W₀ < k → k ≤ W₀ + m → J + (k : ℤ) ≠ 0) →
      Fr.towerShift b n F = C (Fr.ρ ^ J) * F + G →
      TowerObstruction Fr ∨ (WLe n F W₀ ∧ WLe n G W₀) := by
  classical
  intro m
  induction m with
  | zero =>
      intro F G hF hG _ _
      simpa using Or.inr ⟨hF, hG⟩
  | succ m ih =>
      intro F G hF hG hJ hrel
      have hWrw : W₀ + (m + 1) = (W₀ + m) + 1 := by omega
      rw [hWrw] at hF hG
      by_cases htop : ∀ d : Fin n →₀ ℕ,
          Finsupp.weight (jetWeight n) d = (W₀ + m) + 1 → coeff d F = 0
      · have hFW : WLe n F (W₀ + m) := wLe_of_top_vanishing hF htop
        have hGtop : ∀ d : Fin n →₀ ℕ,
            Finsupp.weight (jetWeight n) d = (W₀ + m) + 1 → coeff d G = 0 := by
          intro d hd
          have h := Fr.base_relation_of_towerShift b hF hrel hd
          rw [htop d hd, map_zero, mul_zero, zero_add] at h
          have hpow : (Fr.ρ : K) ^ ((W₀ + m) + 1) ≠ 0 := pow_ne_zero _ Fr.ρ_ne
          exact (mul_eq_zero.mp h.symm).resolve_left hpow
        exact ih F G hFW (wLe_of_top_vanishing hG hGtop)
          (fun k hk hk' => hJ k hk (by omega)) hrel
      · push Not at htop
        obtain ⟨d, hd, hFd⟩ := htop
        have h := Fr.base_relation_of_towerShift b hF hrel hd
        refine Or.inl ?_
        by_cases hGd : (Fr.ρ : K) ^ ((W₀ + m) + 1) * coeff d G = 0
        · rw [hGd, add_zero] at h
          refine Or.inl ⟨coeff d F, J + (((W₀ + m) + 1 : ℕ) : ℤ), hFd,
            hJ ((W₀ + m) + 1) (by omega) (by omega), ?_⟩
          rw [h, zpow_add₀ Fr.ρ_ne, zpow_natCast]
        · exact Or.inr ⟨coeff d F, (Fr.ρ : K) ^ ((W₀ + m) + 1) * coeff d G,
            J + (((W₀ + m) + 1 : ℕ) : ℤ), hFd, hGd, by
              rw [h, zpow_add₀ Fr.ρ_ne, zpow_natCast]⟩

theorem wLe_towerShift (Fr : RittFrame K L) (b : K) {F : MvPolynomial (Fin n) K} {W : ℕ}
    (hF : WLe n F W) : WLe n (Fr.towerShift b n F) W := by
  have h1 := Fr.wLt_towerShift_sub_towerDiagShift b hF
  have h2 : WLe n (Fr.towerDiagShift n F) W := by
    intro e he
    rw [MvPolynomial.mem_support_iff, Fr.coeff_towerDiagShift F e] at he
    refine hF e (MvPolynomial.mem_support_iff.mpr ?_)
    intro h0
    rw [h0, map_zero, zero_mul] at he
    exact he rfl
  have hsplit : Fr.towerShift b n F
      = (Fr.towerShift b n F - Fr.towerDiagShift n F) + Fr.towerDiagShift n F := by ring
  rw [hsplit]
  exact h1.wLe.add h2

/-- **A collapse of the affine tower forces a base obstruction, or the collapsing polynomial is
weighted homogeneous of weight `n + 1` with shift-fixed coefficients.** -/
theorem obstruction_or_weightedHomogeneous_of_collapse (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {F : MvPolynomial (Fin n) K}
    (hcol : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ ^ (n + 1))⁻¹) * aeval (Fr.jetFamily u n) F
        + Fr.towerDefect u b n) :
    TowerObstruction Fr ∨
      (F = weightedHomogeneousComponent (jetWeight n) (n + 1) F ∧
        ∀ d : Fin n →₀ ℕ, Fr.ψ (coeff d F) = coeff d F) := by
  classical
  have hρ : (Fr.ρ : K) ≠ 0 := Fr.ρ_ne
  have hJ : (Fr.ρ : K) ^ (-((n : ℤ) + 1)) = (Fr.ρ ^ (n + 1))⁻¹ := by
    rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hJmul : (Fr.ρ : K) ^ (-((n : ℤ) + 1)) * Fr.ρ ^ (n + 1) = 1 := by
    rw [hJ, inv_mul_cancel₀ (pow_ne_zero _ hρ)]
  have hcol' : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * aeval (Fr.jetFamily u n) F
        + aeval (Fr.jetFamily u n) (Fr.defectPoly b n) := by
    rw [hJ, Fr.aeval_defectPoly u b n]
    exact hcol
  have hpoly : Fr.towerShift b n F
      = C ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * F + Fr.defectPoly b n :=
    Fr.towerShift_eq_of_collapse hu hind hcol'
  set W : ℕ := weightedTotalDegree (jetWeight n) F with hWdef
  have hFtot : WLe n F W := fun e he => le_weightedTotalDegree (jetWeight n) he
  -- descend to the floor `n + 1`
  have hstep := Fr.obstruction_or_wLe_of_towerRelation b (J := -((n : ℤ) + 1)) (n + 1) W F
    (Fr.defectPoly b n) (hFtot.mono (by omega)) ((Fr.wLe_defectPoly b n).mono (by omega))
    (fun k hk _ => by
      intro hzero
      have : (k : ℤ) = (n : ℤ) + 1 := by omega
      have hk' : k = n + 1 := by exact_mod_cast this
      omega) hpoly
  rcases hstep with hobs | ⟨hFn, -⟩
  · exact Or.inl hobs
  -- the top layer is shift-fixed
  have hfix : ∀ d : Fin n →₀ ℕ, Finsupp.weight (jetWeight n) d = n + 1 →
      Fr.ψ (coeff d F) = coeff d F := by
    intro d hd
    have h := Fr.base_relation_of_towerShift b hFn hpoly hd
    have hGd : coeff d (Fr.defectPoly b n) = 0 := by
      by_contra hne
      have := Fr.wLe_defectPoly b n d (MvPolynomial.mem_support_iff.mpr hne)
      omega
    rw [hGd, mul_zero, add_zero] at h
    rw [h, hJmul, one_mul]
  set F1 : MvPolynomial (Fin n) K := weightedHomogeneousComponent (jetWeight n) (n + 1) F with hF1
  set F0 : MvPolynomial (Fin n) K := F - F1 with hF0
  have hF1coeff : ∀ d : Fin n →₀ ℕ, Finsupp.weight (jetWeight n) d = n + 1 →
      coeff d F1 = coeff d F := by
    intro d hd
    rw [hF1, coeff_weightedHomogeneousComponent, if_pos hd]
  have hF1le : WLe n F1 (n + 1) := wLe_weightedHomogeneousComponent (n + 1) F
  have hF0le : WLe n F0 n := by
    have := wLe_sub_weightedHomogeneousComponent hFn
    simpa using this
  set D : MvPolynomial (Fin n) K
    := Fr.towerShift b n F1 - C ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * F1 with hD
  have hDle : WLe n D n := by
    refine wLe_of_top_vanishing ((Fr.wLe_towerShift b hF1le).sub
      ((wLe_C (n := n) ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) 0).mul hF1le |>.mono (by omega))) ?_
    intro d hd
    rw [hD, coeff_sub, coeff_C_mul, Fr.coeff_towerShift_of_top b hF1le hd, hF1coeff d hd,
      hfix d hd, hJ]
    ring
  have hrel0 : Fr.towerShift b n F0
      = C ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * F0 + (Fr.defectPoly b n - D) := by
    rw [hF0, map_sub, hpoly, hD]
    ring
  have hdesc := Fr.obstruction_or_zero_of_towerRelation b (J := -((n : ℤ) + 1)) n F0
    (Fr.defectPoly b n - D) hF0le ((Fr.wLe_defectPoly b n).sub hDle)
    (fun k hk => by
      intro hzero
      have : (k : ℤ) = (n : ℤ) + 1 := by omega
      have hk' : k = n + 1 := by exact_mod_cast this
      omega) hrel0
  rcases hdesc with hobs | ⟨hF0z, -⟩
  · exact Or.inl hobs
  have hFeq : F = F1 := by
    have : F - F1 = 0 := hF0z
    linear_combination (norm := ring_nf) this
  refine Or.inr ⟨hFeq, fun d => ?_⟩
  by_cases hd : Finsupp.weight (jetWeight n) d = n + 1
  · exact hfix d hd
  · have hz : coeff d F = 0 := by
      rw [hFeq, hF1, coeff_weightedHomogeneousComponent, if_neg hd]
    rw [hz, map_zero]

theorem constantCoeff_towerSub (Fr : RittFrame K L) (b : K) (j : Fin n) :
    constantCoeff (Fr.towerSub b n j) = Fr.logConst b (j : ℕ) := by
  classical
  rw [towerSub, map_add, constantCoeff_C]
  have hterm : ∀ i : Fin n,
      constantCoeff (C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i : MvPolynomial (Fin n) K) = 0 := by
    intro i
    rw [map_mul, constantCoeff_C, constantCoeff_X, mul_zero]
  rw [map_sum, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const_zero, zero_add]

theorem constantCoeff_towerShift (Fr : RittFrame K L) (b : K) (F : MvPolynomial (Fin n) K) :
    constantCoeff (Fr.towerShift b n F)
      = eval₂ Fr.ψ (fun j : Fin n => Fr.logConst b (j : ℕ)) F := by
  have hcomp : (constantCoeff : MvPolynomial (Fin n) K →+* K).comp (Fr.towerShift b n)
      = eval₂Hom Fr.ψ (fun j : Fin n => Fr.logConst b (j : ℕ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, Fr.towerShift_C, constantCoeff_C, eval₂Hom_C]
    · rw [RingHom.comp_apply, Fr.towerShift_X, Fr.constantCoeff_towerSub, eval₂Hom_X']
  exact congrFun (congrArg DFunLike.coe hcomp) F

theorem constantCoeff_defectPoly (Fr : RittFrame K L) (b : K) (n : ℕ) :
    constantCoeff (Fr.defectPoly b n) = Fr.logConst b n := by
  classical
  rw [defectPoly, map_add, constantCoeff_C]
  have hterm : ∀ j : Fin n,
      constantCoeff (C (Fr.logCoeff n (j : ℕ)) * X j : MvPolynomial (Fin n) K) = 0 := by
    intro j
    rw [map_mul, constantCoeff_C, constantCoeff_X, mul_zero]
  rw [map_sum, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const_zero, zero_add]

/-- **The residual equation of a collapse.**  Either a base obstruction exists, or the collapsing
polynomial takes the tower's base constants to the next one. -/
theorem eval_logConst_of_collapse (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {F : MvPolynomial (Fin n) K}
    (hcol : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ ^ (n + 1))⁻¹) * aeval (Fr.jetFamily u n) F
        + Fr.towerDefect u b n) :
    TowerObstruction Fr ∨
      eval (fun j : Fin n => Fr.logConst b (j : ℕ)) F = Fr.logConst b n := by
  classical
  rcases Fr.obstruction_or_weightedHomogeneous_of_collapse hu hind hcol with hobs | ⟨hhom, hfix⟩
  · exact Or.inl hobs
  refine Or.inr ?_
  have hρ : (Fr.ρ : K) ≠ 0 := Fr.ρ_ne
  have hJ : (Fr.ρ : K) ^ (-((n : ℤ) + 1)) = (Fr.ρ ^ (n + 1))⁻¹ := by
    rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hcol' : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * aeval (Fr.jetFamily u n) F
        + aeval (Fr.jetFamily u n) (Fr.defectPoly b n) := by
    rw [hJ, Fr.aeval_defectPoly u b n]
    exact hcol
  have hpoly : Fr.towerShift b n F
      = C ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * F + Fr.defectPoly b n :=
    Fr.towerShift_eq_of_collapse hu hind hcol'
  have hF0 : coeff (0 : Fin n →₀ ℕ) F = 0 := by
    have hw : Finsupp.weight (jetWeight n) (0 : Fin n →₀ ℕ) ≠ n + 1 := by simp
    conv_lhs => rw [hhom]
    rw [coeff_weightedHomogeneousComponent, if_neg hw]
  have hmapF : (map Fr.ψ F : MvPolynomial (Fin n) K) = F := by
    ext d
    rw [coeff_map]
    exact hfix d
  have hconst := congrArg (constantCoeff : MvPolynomial (Fin n) K →+* K) hpoly
  rw [Fr.constantCoeff_towerShift b F, map_add, map_mul, constantCoeff_C,
    Fr.constantCoeff_defectPoly b n, constantCoeff_apply, hF0, mul_zero, zero_add] at hconst
  rw [eval₂_eq_eval_map, hmapF] at hconst
  exact hconst

end RittFrame

end GaloisForLFunctions.HTGeometry
