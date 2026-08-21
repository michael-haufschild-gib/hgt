/-
# The collision bound of the fully coupled shortcut law

Inside the tube over a patch of the diagonal carrier the Hamiltonian is a bounded perturbation of a
*diagonal* Hamiltonian, so the flat-overlap bound applies verbatim: if the carrier energies of the
patch are separated by `γ` and the tube radius is `r`, then the uniform superposition has spectral
collision at most `(D^{-1/2} + 2Lr/γ)²` for every Hamiltonian of the tube, where `L` is the
Lipschitz constant of the coefficient-to-Hamiltonian map.  No seed selection and no genericity are
needed: the bound is deterministic on the whole tube.

Main results:
* `pathPatchEquiv_symm_notDiag`, `pathPatchIsometry_embed_offDiag` — the embedded patch lies in the
  carrier.
* `patchHamLM_embed_eq_diagonal` — **the patch Hamiltonian is diagonal**.
* `spectralCollision_uniformSeed_le_of_mem_patchThickening` — **`(22)` on the tube**.
-/
import GaloisForLFunctions.HTGeometry.CapacityIncubationInstantiation
import GaloisForLFunctions.HTGeometry.NearUniformSeparatingCarrier

open Matrix Finset Metric Set _root_.HTGeometry
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

theorem pathPatchEquiv_symm_notDiag {l : PathLabel n} (hl : ¬ IsDiagLabel l) :
    ∃ j, (pathPatchEquiv n).symm l = Sum.inr j := by
  classical
  obtain ⟨j0, hj0⟩ : ∃ j0, (Equiv.sumCompl (IsDiagLabel (n := n))).symm l = Sum.inr j0 :=
    ⟨⟨l, hl⟩, by
      have : (Equiv.sumCompl (IsDiagLabel (n := n))) (Sum.inr ⟨l, hl⟩) = l := rfl
      exact (Equiv.symm_apply_eq _).mpr this.symm⟩
  refine ⟨Fintype.equivFinOfCardEq (card_offDiagLabel n) j0, ?_⟩
  show (Equiv.sumCongr (Fintype.equivFinOfCardEq (card_diagLabel n)).symm
      (Fintype.equivFinOfCardEq (card_offDiagLabel n)).symm).symm
      ((Equiv.sumCompl (IsDiagLabel (n := n))).symm l) = _
  rw [hj0]
  rfl

/-- The embedded patch lies inside the diagonal carrier. -/
theorem pathPatchIsometry_embed_offDiag (v : EuclideanSpace ℝ (Fin (2 * n + 3)))
    {l : PathLabel n} (hl : ¬ IsDiagLabel l) :
    pathPatchIsometry n (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12))))) l = 0 := by
  obtain ⟨j, hj⟩ := pathPatchEquiv_symm_notDiag hl
  rw [ofLp_pathPatchIsometry_embed, hj]
  rfl

variable {k : ℕ}

/-- **The patch Hamiltonian is diagonal.** -/
theorem patchHamLM_embed_eq_diagonal (v : EuclideanSpace ℝ (Fin (2 * (k + 1) + 3))) :
    patchHamLM k (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))
      = Matrix.diagonal fun x => ((pathDiagEnergy
          (pathPatchIsometry (k + 1)
            (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))) x : ℝ) : ℂ) := by
  rw [patchHamLM_apply]
  exact pathHamiltonian_eq_diagonal _ fun l hl => pathPatchIsometry_embed_offDiag v hl

/-- **`(22)` on the tube.**  Every Hamiltonian of the tube over a separated carrier patch keeps the
uniform superposition capacity-good. -/
theorem spectralCollision_uniformSeed_le_of_mem_patchThickening
    {PU : Set (EuclideanSpace ℝ (Fin (2 * (k + 1) + 3)))}
    (hcompact : IsCompact (embedPatch (d := 10 * (k + 1) + 12) PU))
    (hnonempty : (embedPatch (d := 10 * (k + 1) + 12) PU).Nonempty)
    {gap r : ℝ} (hgap : 0 < gap) (hr : 0 ≤ r)
    (hsep : ∀ v ∈ PU, ∀ x y : FiniteQubitConfiguration (Fin (k + 3)), x ≠ y →
      gap ≤ |pathDiagEnergy (pathPatchIsometry (k + 1)
              (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))) x
            - pathDiagEnergy (pathPatchIsometry (k + 1)
              (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))) y|)
    {ω : sphere (0 : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) 1}
    (hω : ω ∈ patchThickening (d := 10 * (k + 1) + 12) PU r)
    {ebasis : FiniteQubitConfiguration (Fin (k + 3)) → FiniteQubitConfiguration (Fin (k + 3)) → ℂ}
    {lam : FiniteQubitConfiguration (Fin (k + 3)) → ℝ}
    (heb : IsOrthoEigenBasis (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3)
      (10 * (k + 1) + 12))) ebasis lam) :
    spectralCollision ebasis (uniformSeed (k + 3))
      ≤ ((Real.sqrt (2 ^ (k + 3)))⁻¹
          + 2 * (Real.sqrt (Fintype.card (PathLabel (k + 1))) * r) / gap) ^ 2 := by
  classical
  obtain ⟨y, hy, hdist⟩ :=
    hcompact.exists_infDist_eq_dist hnonempty
      (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))
  obtain ⟨v, hvPU, hvy⟩ := hy
  have hle : dist (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) y ≤ r := by
    rw [← hdist]
    exact hω
  have hnear : ‖patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))
      - Matrix.diagonal (fun x => ((pathDiagEnergy (pathPatchIsometry (k + 1)
          (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))) x : ℝ) : ℂ))‖
      ≤ Real.sqrt (Fintype.card (PathLabel (k + 1))) * r := by
    have hvy' : (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))) :
        PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) = y := hvy
    rw [← patchHamLM_embed_eq_diagonal v, hvy']
    refine le_trans (norm_patchHamLM_sub_le k _ y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [← dist_eq_norm]
    exact hle
  have hdelta : (0 : ℝ) ≤ Real.sqrt (Fintype.card (PathLabel (k + 1))) * r :=
    mul_nonneg (Real.sqrt_nonneg _) hr
  have hchi : ∀ x, ‖uniformSeed (k + 3) x‖ ≤ (Real.sqrt (2 ^ (k + 3)))⁻¹ := fun x =>
    le_of_eq (norm_uniformSeed (k + 3) x)
  have hc : (0 : ℝ) ≤ (Real.sqrt (2 ^ (k + 3)))⁻¹ := by positivity
  exact spectralCollision_le_of_near_diagonal hgap
    (fun x z hxz => hsep v hvPU x z hxz) hdelta hnear heb hc hchi
    (norm_eucVec_uniformSeed (k + 3))


/-! ## The carrier direction in patch coordinates -/

section PatchDir

variable {f d : ℕ}

/-- The embedding of the carrier factor is an isometry onto its image. -/
theorem norm_embedPatch_sub (a b : EuclideanSpace ℝ (Fin f)) :
    ‖(WithLp.toLp 2 (a, (0 : EuclideanSpace ℝ (Fin d))) : PatchSpace f d)
      - WithLp.toLp 2 (b, (0 : EuclideanSpace ℝ (Fin d)))‖ = ‖a - b‖ := by
  have h : (WithLp.toLp 2 (a, (0 : EuclideanSpace ℝ (Fin d))) : PatchSpace f d)
      - WithLp.toLp 2 (b, (0 : EuclideanSpace ℝ (Fin d)))
      = WithLp.toLp 2 (a - b, (0 : EuclideanSpace ℝ (Fin d))) := by
    apply WithLp.ofLp_injective
    ext <;> simp
  rw [h, WithLp.prod_norm_eq_add (by norm_num)]
  show (‖a - b‖ ^ (2:ℝ) + ‖(0 : EuclideanSpace ℝ (Fin d))‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) = ‖a - b‖
  rw [norm_zero, Real.zero_rpow (by norm_num), add_zero, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

end PatchDir

theorem ofLp_pathPatchIsometry (p : PatchSpace (2 * n + 3) (10 * n + 12)) (l : PathLabel n) :
    WithLp.ofLp (pathPatchIsometry n p) l
      = Sum.elim (WithLp.ofLp (WithLp.ofLp p).1) (WithLp.ofLp (WithLp.ofLp p).2)
          ((pathPatchEquiv n).symm l) := rfl

theorem notDiag_pathPatchEquiv_inr (j : Fin (10 * n + 12)) :
    ¬ IsDiagLabel (pathPatchEquiv n (Sum.inr j)) :=
  ((Fintype.equivFinOfCardEq (card_offDiagLabel n)).symm j).2

/-- The near-uniform carrier direction, read in the patch coordinates. -/
def carrierPatchDir (n : ℕ) (eps : ℝ) : EuclideanSpace ℝ (Fin (2 * n + 3)) :=
  (WithLp.ofLp ((pathPatchIsometry n).symm (nearUniformDir n eps))).1

theorem embed_carrierPatchDir (eps : ℝ) :
    (WithLp.toLp 2 (carrierPatchDir n eps,
        (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))) : PatchSpace (2 * n + 3) (10 * n + 12))
      = (pathPatchIsometry n).symm (nearUniformDir n eps) := by
  apply WithLp.ofLp_injective
  refine Prod.ext rfl ?_
  show (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))
    = (WithLp.ofLp ((pathPatchIsometry n).symm (nearUniformDir n eps))).2
  apply WithLp.ofLp_injective
  funext j
  have hval := ofLp_pathPatchIsometry ((pathPatchIsometry n).symm (nearUniformDir n eps))
    (pathPatchEquiv n (Sum.inr j))
  rw [LinearIsometryEquiv.apply_symm_apply, Equiv.symm_apply_apply] at hval
  have hzero := nearUniformDir_offDiag (n := n) (eps := eps)
    (pathPatchEquiv n (Sum.inr j)) (notDiag_pathPatchEquiv_inr j)
  rw [hzero] at hval
  exact hval

theorem pathPatchIsometry_embed_carrierPatchDir (eps : ℝ) :
    pathPatchIsometry n (WithLp.toLp 2 (carrierPatchDir n eps,
        (0 : EuclideanSpace ℝ (Fin (10 * n + 12))))) = nearUniformDir n eps := by
  rw [embed_carrierPatchDir, LinearIsometryEquiv.apply_symm_apply]

theorem norm_carrierPatchDir {eps : ℝ} (heps : 0 ≤ eps) (hsmall : eps * 3 ^ (n + 2) ≤ 1) :
    ‖carrierPatchDir n eps‖ = 1 := by
  have h : ‖(WithLp.toLp 2 (carrierPatchDir n eps,
      (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))) : PatchSpace (2 * n + 3) (10 * n + 12))‖
      = ‖carrierPatchDir n eps‖ := by
    have hz : (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (2 * n + 3))),
        (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))) :
        PatchSpace (2 * n + 3) (10 * n + 12)) = 0 := by
      apply WithLp.ofLp_injective
      ext <;> simp
    have hb := norm_embedPatch_sub (d := 10 * n + 12) (carrierPatchDir n eps) 0
    rw [hz, sub_zero] at hb
    rwa [sub_zero] at hb
  rw [← h, embed_carrierPatchDir, LinearIsometryEquiv.norm_map]
  exact norm_nearUniformDir heps hsmall

/-- **The cap around the carrier direction has separated energies.** -/
theorem separation_on_carrierPatchCap {eps rho : ℝ} (heps : 0 < eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 2 / 3)
    (hrho : (2 * (n : ℝ) + 3) * rho ≤ eps / (4 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ)))
    {v : EuclideanSpace ℝ (Fin (2 * n + 3))} (hv : v ∈ sphericalCap (carrierPatchDir n eps) rho)
    {x y : FiniteQubitConfiguration (Fin (n + 2))} (hxy : x ≠ y) :
    eps / (2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ))
      ≤ |pathDiagEnergy (pathPatchIsometry n
            (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))) x
        - pathDiagEnergy (pathPatchIsometry n
            (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))) y| := by
  have hdist : ‖pathPatchIsometry n (WithLp.toLp 2 (v,
      (0 : EuclideanSpace ℝ (Fin (10 * n + 12))))) - nearUniformDir n eps‖ ≤ rho := by
    rw [← pathPatchIsometry_embed_carrierPatchDir (n := n) eps, ← LinearIsometryEquiv.map_sub,
      LinearIsometryEquiv.norm_map, norm_embedPatch_sub]
    have := hv.2
    rwa [dist_eq_norm] at this
  exact gap_near_nearUniformDir heps hsmall hdist hrho hxy


/-! ## The strong-bond clause at a general direction -/

theorem sphericalCap_coord_ge_of {f : ℕ} {dir : EuclideanSpace ℝ (Fin f)} {bmin rho : ℝ}
    (hdir : ∀ i, bmin ≤ WithLp.ofLp dir i) {w : EuclideanSpace ℝ (Fin f)}
    (hw : w ∈ sphericalCap dir rho) (i : Fin f) :
    bmin - rho ≤ WithLp.ofLp w i := by
  have hd : |WithLp.ofLp w i - WithLp.ofLp dir i| ≤ rho := by
    refine le_trans ?_ hw.2
    rw [dist_eq_norm]
    exact abs_coord_le_norm (w - dir) i
  have hab := abs_le.mp hd
  linarith [hab.1, hdir i]

theorem isDiag_pathPatchEquiv_inl (i : Fin (2 * n + 3)) :
    IsDiagLabel (pathPatchEquiv n (Sum.inl i)) :=
  ((Fintype.equivFinOfCardEq (card_diagLabel n)).symm i).2

theorem carrierPatchDir_coord_ge {eps : ℝ} (heps : 0 ≤ eps) (hsmall : eps * 3 ^ (n + 2) ≤ 1)
    (i : Fin (2 * n + 3)) :
    (2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ))⁻¹ ≤ WithLp.ofLp (carrierPatchDir n eps) i := by
  have hval : WithLp.ofLp (carrierPatchDir n eps) i
      = nearUniformDir n eps (pathPatchEquiv n (Sum.inl i)) := by
    have hv := ofLp_pathPatchIsometry ((pathPatchIsometry n).symm (nearUniformDir n eps))
      (pathPatchEquiv n (Sum.inl i))
    rw [LinearIsometryEquiv.apply_symm_apply, Equiv.symm_apply_apply] at hv
    exact hv.symm
  rw [hval]
  exact nearUniformDir_coord_ge heps hsmall _ (isDiag_pathPatchEquiv_inl i)

/-- **`(25)` at the carrier direction.**  Inside the tube over the cap every edge stays coupled. -/
theorem edgeCoupling_lower_carrier {eps rho r : ℝ} (heps : 0 ≤ eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 1)
    {u : PathShell n} {w : EuclideanSpace ℝ (Fin (2 * n + 3))}
    (hw : w ∈ sphericalCap (carrierPatchDir n eps) rho)
    (hdist : ‖u - pathPatchIsometry n
      (WithLp.toLp 2 (w, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))‖ ≤ r)
    (e : Fin (n + 1)) :
    (2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ))⁻¹ - rho - r ≤ ‖edgePart u e‖ := by
  classical
  obtain ⟨y, hydef⟩ : ∃ y : PathShell n, y = pathPatchIsometry n
    (WithLp.toLp 2 (w, (0 : EuclideanSpace ℝ (Fin (10 * n + 12))))) := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l : PathLabel n, l = Sum.inr (e, ((2 : Fin 3), (2 : Fin 3))) := ⟨_, rfl⟩
  have hldiag : IsDiagLabel l := by rw [hldef]; rfl
  obtain ⟨i, hi⟩ := pathPatchEquiv_symm_isDiag hldiag
  have hy : WithLp.ofLp y l = WithLp.ofLp w i := by
    rw [hydef, ofLp_pathPatchIsometry_embed, hi]
    rfl
  have hylow : (2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ))⁻¹ - rho ≤ WithLp.ofLp y l := by
    rw [hy]
    exact sphericalCap_coord_ge_of (carrierPatchDir_coord_ge heps hsmall) hw i
  have hclose : |WithLp.ofLp u l - WithLp.ofLp y l| ≤ r := by
    rw [hydef]
    exact le_trans (abs_coord_le_norm (u - pathPatchIsometry n
      (WithLp.toLp 2 (w, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))) l) hdist
  have hcoef : (2 * Real.sqrt ((2 * n + 3 : ℕ) : ℝ))⁻¹ - rho - r ≤ WithLp.ofLp u l := by
    have := abs_le.mp hclose
    linarith [this.1, hylow]
  have hrho : |edgeCoeff u e ((2 : Fin 3), (2 : Fin 3))| ≤ edgeRho (edgeCoeff u e) :=
    abs_edgeCoeff_le_edgeRho _ _
  have hval : edgeCoeff u e ((2 : Fin 3), (2 : Fin 3)) = WithLp.ofLp u l := by
    rw [hldef]
    rfl
  have hop : edgeRho (edgeCoeff u e) ≤ ‖edgePart u e‖ := edgeRho_le_norm_edgePart u e
  have habs : WithLp.ofLp u l ≤ |edgeCoeff u e ((2 : Fin 3), (2 : Fin 3))| := by
    rw [hval]
    exact le_abs_self _
  linarith [hcoef, habs, hrho, hop]


/-! ## Theorem C on the tube -/

section TheoremC

variable {k : ℕ}

/-- **Theorem C on the tube.**  Every Hamiltonian of the tube over the separated diagonal patch
incubates the fixed uniform superposition through `L`, keeps its spectral collision `O(1/D)`, and
has every spatial bond strongly coupled.  No seed is selected and no genericity is used. -/
theorem coupled_shortcut_tube {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))))
    (chi : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))))
    {eps rho r L eta epsMinus : ℝ} {B : ℕ}
    (heps : 0 < eps) (hsmall : eps * 3 ^ ((k + 1) + 2) ≤ 2 / 3)
    (hrho0 : 0 ≤ rho) (hr0 : 0 ≤ r)
    (hrho : (2 * (((k + 1 : ℕ) : ℝ)) + 3) * rho
      ≤ eps / (4 * Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ)))
    (hcert : ∀ y ∈ embedPatch (d := 10 * (k + 1) + 12)
        (sphericalCap (carrierPatchDir (k + 1) eps) rho),
      ∀ s : ℝ, ∃ w : List Γ, w.length ≤ B ∧
        dist (orbitState (patchHamLM k y) (eucVec (uniformSeed (k + 3))) s)
          (wordAct act w chi) ≤ eta)
    (hL : 0 ≤ L)
    (hgap : L * (Real.sqrt (Fintype.card (PathLabel (k + 1))) * r) ≤ epsMinus - eta)
    {ω : sphere (0 : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) 1}
    (hω : ω ∈ patchThickening (d := 10 * (k + 1) + 12)
      (sphericalCap (carrierPatchDir (k + 1) eps) rho) r) :
    (∀ t : ℝ, 0 ≤ t → t ≤ L → approxComplexity act chi epsMinus
        (orbitState (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
          (eucVec (uniformSeed (k + 3))) t) ≤ B)
    ∧ (∀ ebasis lam, IsOrthoEigenBasis
          (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) ebasis lam →
        spectralCollision ebasis (uniformSeed (k + 3))
          ≤ ((Real.sqrt (2 ^ (k + 3)))⁻¹
              + 2 * (Real.sqrt (Fintype.card (PathLabel (k + 1))) * r)
                / (eps / (2 * Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ)))) ^ 2)
    ∧ (∀ e : Fin (k + 2), (2 * Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ))⁻¹ - rho - r
        ≤ ‖edgePart (pathPatchIsometry (k + 1)
            (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) e‖) := by
  classical
  have hone : (1 : ℝ) ≤ 3 ^ ((k + 1) + 2) := one_le_pow₀ (by norm_num)
  have hsmall1 : eps * 3 ^ ((k + 1) + 2) ≤ 1 := by linarith
  have hdirnorm : ‖carrierPatchDir (k + 1) eps‖ = 1 := norm_carrierPatchDir heps.le hsmall1
  have hcompact := isCompact_embedPatch_sphericalCap (d := 10 * (k + 1) + 12)
    (carrierPatchDir (k + 1) eps) rho
  have hnonempty := nonempty_embedPatch_sphericalCap (d := 10 * (k + 1) + 12) hdirnorm hrho0
  have hgappos : 0 < eps / (2 * Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ)) := by
    have hsq : (0 : ℝ) < Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ) := by
      refine Real.sqrt_pos.mpr ?_
      positivity
    positivity
  refine ⟨?_, ?_, ?_⟩
  · intro t ht0 htL
    exact approxComplexity_le_of_mem_patchThickening act chi
      (norm_eucVec_uniformSeed (k + 3)) (patchHamLM k) (fun p => isSelfAdjoint_patchHamLM k p)
      (Real.sqrt_nonneg _) (fun a b => norm_patchHamLM_sub_le k a b) hcompact hnonempty
      hcert hL hgap hω ht0 htL
  · intro ebasis lam heb
    exact spectralCollision_uniformSeed_le_of_mem_patchThickening hcompact hnonempty
      hgappos hr0
      (fun v hv x y hxy => separation_on_carrierPatchCap heps hsmall hrho hv hxy) hω heb
  · intro e
    obtain ⟨y, hy, hdist⟩ :=
      hcompact.exists_infDist_eq_dist hnonempty
        (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))
    obtain ⟨v, hvcap, hvy⟩ := hy
    have hvy' : (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))) :
        PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) = y := hvy
    have hle : dist (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) y ≤ r := by
      rw [← hdist]
      exact hω
    have hdist' : ‖pathPatchIsometry (k + 1)
        (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))
        - pathPatchIsometry (k + 1)
          (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))‖ ≤ r := by
      rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map, hvy', ← dist_eq_norm]
      exact hle
    exact edgeCoupling_lower_carrier heps.le hsmall1 hvcap hdist' e

end TheoremC

end GaloisForLFunctions.HTGeometry

end
