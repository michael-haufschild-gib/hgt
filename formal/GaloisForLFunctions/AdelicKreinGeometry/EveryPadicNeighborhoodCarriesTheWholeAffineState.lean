import GaloisForLFunctions.AdelicKreinGeometry.EveryPadicNeighborhoodCarriesTheWholeIndex
import GaloisForLFunctions.ArithmeticCouplingTheory.MixedDifferencesSeeEveryZero
import GaloisForLFunctions.AdelicKreinGeometry.TheGluingFormulaAtEveryPlace
import GaloisForLFunctions.ArithmeticPositiveDuality.AContinuousArchimedeanSpectrumIsSeenByTheSuccessor

/-!
# Principal-unit restrictions preserve the affine Weil index

Dense logarithmic scales retain every Weil negative square on coefficient families
of total mass zero. For positive p-adic principal-unit slopes, this is also the
place-polar hyperplane. The subgroup gluing formula then supplies the independent
successor square using rational translations, giving the exact global affine index
at every principal-unit resolution.
-/

open Complex Finset
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCouplingTheory
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A difference family has total mass zero, so its index is bounded by the polar index. -/
theorem negIndex_lap_le_polarIndex {G : Type*} [CommGroup G] (a : G) (K : G → ℂ) :
    negIndex (lap a K) ≤ polarIndex K := by
  classical
  refine negIndex_le_iff.mpr fun n x => ?_
  let e : Fin (Fintype.card (Fin n ⊕ Fin n)) ≃ (Fin n ⊕ Fin n) :=
    (Fintype.equivFin _).symm
  let y := Sum.elim x (fun i => x i * a)
  let L : (Fin n → ℂ) →ₗ[ℂ] (Fin (Fintype.card (Fin n ⊕ Fin n)) → ℂ) :=
    { toFun := fun c j => Sum.elim c (fun i => -c i) (e j)
      map_add' := fun c d => by funext j; cases h : e j <;> simp [h, add_comm]
      map_smul' := fun t c => by funext j; cases h : e j <;> simp [h] }
  have hmass (c : Fin n → ℂ) : L c ∈ LinearMap.ker (totalMass _) := by
    change (∑ j, Sum.elim c (fun i => -c i) (e j)) = 0
    rw [e.sum_comp]
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sum_neg_distrib,
      add_neg_cancel]
  have hquad (c : Fin n → ℂ) :
      hermQuad (gram K (y ∘ e)) (L c) = hermQuad (gram (lap a K) x) c := by
    change hermQuad ((gram K y).submatrix e e) (L c) = _
    rw [HeckeKreinToeplitz.hermQuad_submatrix_equiv, hermQuad_gram_lap]
    congr 1
    funext j
    simp only [L, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, e.apply_symm_apply]
  obtain ⟨W, hWr, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-gram (lap a K) x)
  let bW := Module.finBasis ℂ W
  let M := L ∘ₗ W.subtype ∘ₗ bW.equivFun.symm.toLinearMap
  have hneg : ∀ β, β ≠ 0 → hermQuad (gram K (y ∘ e)) (M β) < 0 := by
    intro β hβ
    have hw0 : (bW.equivFun.symm β : Fin n → ℂ) ≠ 0 := fun h =>
      hβ (bW.equivFun.symm.injective ((Subtype.ext h).trans (map_zero _).symm))
    change hermQuad (gram K (y ∘ e)) (L (bW.equivFun.symm β)) < 0
    rw [hquad]
    have h := hW _ (bW.equivFun.symm β).2 hw0
    rw [hermQuad_neg] at h
    linarith only [h]
  have h := card_le_negIndexOn_of_forall_neg (gram K (y ∘ e))
    (LinearMap.ker (totalMass _)) M (fun β => hmass _) hneg
  rw [Fintype.card_fin] at h
  have hr : Module.finrank ℂ W = hermNegIndex (gram (lap a K) x) := hWr
  rw [hr] at h
  exact (Nat.cast_le.mpr h).trans (negIndexOn_le_polarIndex K (y ∘ e))

private theorem lap_comp {G H : Type*} [CommGroup G] [CommGroup H]
    (φ : G →* H) (a : G) (K : H → ℂ) :
    lap a (K ∘ φ) = lap (φ a) K ∘ φ := by
  funext g
  simp only [lap, Function.comp_apply, map_mul, map_inv]

/-- A subgroup with dense logarithmic scales retains every Weil square on its mass-zero families. -/
theorem polarIndex_ratCorr_of_dense_log (H : Subgroup posUnits)
    (hdense : ∀ (t : ℝ) {ε : ℝ}, 0 < ε → ∃ u : H, |logPos (u : posUnits) - t| < ε) :
    polarIndex (ratCorr ∘ H.subtype) = negIndex ratCorr := by
  let φ := posUnitsToHecke.comp H.subtype
  have hD : ArithmeticCastelnuovoSeveri.DenseShifts
      (Set.range fun u => scale heckeLogScale (φ u)) := by
    intro t _ ε hε
    obtain ⟨u, hu⟩ := hdense t hε
    exact ⟨logPos (u : posUnits), ⟨u, rfl⟩, hu⟩
  obtain ⟨a, ha⟩ := hdense 1 (by norm_num : (0 : ℝ) < 1 / 2)
  have hscale : scale heckeLogScale (φ a) ≠ 0 := by
    change logPos (a : posUnits) ≠ 0
    intro hz
    rw [hz] at ha
    norm_num at ha
  have he : ratCorr ∘ H.subtype =
      orbitKernel Zeta23.zetaZeroConfig BiScaleUncertainty.ChebyshevGauge.cubicSpline ∘ φ := by
    funext u
    exact ratCorr_eq_zetaKernel u
  have hindex : negIndex (lap a (lap a (ratCorr ∘ H.subtype))) =
      negIndex ratCorr := by
    rw [he, lap_comp, lap_comp,
      ← orbitKernel_mixedDiff _ SquareRootThreshold.temperedConfig_zetaZeroConfig
        cubicSpline_mem_realTests]
    rw [negIndex_orbitKernel_comp _ SquareRootThreshold.temperedConfig_zetaZeroConfig
      (mixedDiff_mem_realTests cubicSpline_mem_realTests _ _) φ hD,
      seenRightZeros_mixedDiff _ cubicSpline_mem_realTests hscale hscale,
      ArithmeticOrientationGeometry.seenRightZeros_cubicSpline,
      negIndex_ratCorr, negIndex_zetaKernel]
    rfl
  refine le_antisymm ((polarIndex_le_negIndex _).trans
    (negIndex_comp_le ratCorr H.subtype)) ?_
  rw [← hindex]
  exact (negIndex_lap_le a _).trans (negIndex_lap_le_polarIndex a _)

variable (p : ℕ) [Fact p.Prime]

/-- Removing the constant direction inside any p-adic principal-unit group loses no Weil square. -/
theorem polarIndex_ratCorr_padicPrincipalUnits (n : ℕ) :
    polarIndex (ratCorr ∘ (padicPrincipalUnits p n).subtype) = negIndex ratCorr :=
  polarIndex_ratCorr_of_dense_log _ (exists_padicPrincipalUnit_log_near p n)

/-- Rational affine transformations with positive principal-unit slope. -/
def principalUnitAffine (n : ℕ) : Subgroup AffineGroupQ :=
  posAffine ⊓ (padicPrincipalUnits p n).comap slopeAbs

private theorem dilation_mem_principalUnitAffine (n : ℕ) (u : padicPrincipalUnits p n) :
    dilation ((u : posUnits) : ℚˣ) ∈ principalUnitAffine p n := by
  constructor
  · change 0 < affSlope (dilation ((u : posUnits) : ℚˣ))
    rw [affSlope_dilation]
    exact (u : posUnits).2
  · change slopeAbs (dilation ((u : posUnits) : ℚˣ)) ∈ padicPrincipalUnits p n
    rw [slopeAbs_dilation]
    exact u.2

private theorem translation_mem_principalUnitAffine (n : ℕ) (t : ℚ) :
    translation t ∈ principalUnitAffine p n := by
  constructor
  · change 0 < affSlope (translation t)
    rw [affSlope_translation]
    exact zero_lt_one
  · change slopeAbs (translation t) ∈ padicPrincipalUnits p n
    rw [slopeAbs_translation]
    exact (padicPrincipalUnits p n).one_mem

private theorem placeMass_principalUnits (n : ℕ) {m : ℕ}
    (u : Fin m → padicPrincipalUnits p n) :
    placeMass (Rat.AbsoluteValue.padic p) 1 (fun i => (u i : posUnits)) = totalMass (Fin m) := by
  apply LinearMap.ext
  intro w
  change (∑ i, w i * (((Rat.AbsoluteValue.padic p (((u i : posUnits) : ℚˣ) : ℚ)) ^
    (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = ∑ i, w i
  apply sum_congr rfl
  intro i _
  rw [(u i).2.1, Real.one_rpow, Complex.ofReal_one, mul_one]

/-- The native p-adic affine state retains every global square and its successor square
after any principal-unit restriction of positive slopes. -/
theorem negIndex_weilPadicState_principalUnits (n : ℕ) {c : ℝ} (hc : 0 < c) :
    negIndex (weilPadicState p c ∘ (principalUnitAffine p n).subtype) = negIndex ratCorr + 1 := by
  let K := ratCorr ∘ (padicPrincipalUnits p n).subtype
  let Φ := weilPadicState p c ∘ (principalUnitAffine p n).subtype
  have hupper : negIndex Φ ≤ negIndex ratCorr + 1 := by
    exact (negIndex_comp_le (weilPadicState p c) (principalUnitAffine p n).subtype).trans
      (by rw [negIndex_weilPadicState_eq p hc, negIndex_ratCorr])
  refine le_antisymm hupper ?_
  have hfamily (m : ℕ) (u : Fin m → padicPrincipalUnits p n) :
      (negIndexOn (gram K u) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) + 1 ≤ negIndex Φ := by
    have h := add_one_le_negIndex_glueAt_subgroup (isGluingSuccessor_negUltra p hc) one_pos
      ⟨_, one_lt_padic_inv p⟩ isHermKernel_ratCorr (fun i => (u i : posUnits))
      (principalUnitAffine p n) (fun i => dilation_mem_principalUnitAffine p n (u i))
      (translation_mem_principalUnitAffine p n)
    rw [placeMass_principalUnits] at h
    exact h
  rcases eq_or_ne (negIndex Φ) ⊤ with htop | htop
  · rw [htop]
    exact le_top
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp htop
  have hfinite (m : ℕ) (u : Fin m → padicPrincipalUnits p n) :
      negIndexOn (gram K u) (LinearMap.ker (totalMass (Fin m))) + 1 ≤ M := by
    have h := hfamily m u
    rw [← hM] at h
    exact_mod_cast h
  have h1 : 1 ≤ M := by
    have h := hfinite 0 (fun i => i.elim0)
    omega
  have hall (m : ℕ) (u : Fin m → padicPrincipalUnits p n) :
      (negIndexOn (gram K u) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) ≤ ((M - 1 : ℕ) : ℕ∞) :=
    Nat.cast_le.mpr (by have h := hfinite m u; omega)
  calc negIndex ratCorr + 1 = polarIndex K + 1 := by rw [polarIndex_ratCorr_padicPrincipalUnits]
    _ ≤ ((M - 1 : ℕ) : ℕ∞) + 1 := add_le_add (iSup₂_le hall) le_rfl
    _ = negIndex Φ := by rw [← hM]; norm_cast; omega

end GaloisForLFunctions.AdelicKreinGeometry
