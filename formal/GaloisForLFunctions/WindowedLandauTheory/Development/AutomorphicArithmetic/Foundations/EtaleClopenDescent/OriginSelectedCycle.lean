import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginColumnModels
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SelectedBoundaryDescent

/-! A regular top form at the origin extends to a Koszul cocycle
when its coefficient times every extra weight vanishes on the origin fibre. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD
open scoped GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k F L ι : Type} [Field k] [CharZero k] [IsAlgClosed k] [Field F] [Field L]
  [LinearOrder ι] [Fintype ι] [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  {d : ℕ} {x : Fin (d + 1) → F}

local notation "B₀" => rB k L x {0}

/-- Point-local residue tests lift the prescribed origin coefficient
through the extra equations of the affine Koszul complex. -/
theorem exists_chartKoszulCycle_of_originValue (hL : IsFinCover k L x)
    [IsReduced (B₀ ⧸ originIdeal k L x)]
    (B : Subalgebra k L) [Algebra.FiniteType k B] (r : ι → B) (sel : Fin d ↪o ι)
    (hmodel : ∀ e : B →ₐ[k] k, (∀ j, e (r (sel j)) = 0) →
      ∃ f : OriginFibrePoint k L x, ∀ a b, Val B e a b ↔ Val B₀ f.1 a b)
    (hsel : ∀ j, (r (sel j) : L) = algebraMap F L (x j.succ / x 0))
    (hvol : originAffineVolume k L x ∈ omB k L B d)
    (a : B) (hann : ∀ (e : B →ₐ[k] k), (∀ j, e (r (sel j)) = 0) →
      ∀ l ∉ selectedIndices sel, e (r l) * e a = 0) :
    let w := fun l => Algebra.lsmul k k (DR k L) (r l : L)
    ∃ c ∈ (acx (fun _ => omB k L B d) w).Z (d : ℤ),
      c (selectedIndices sel) = (a : L) • originAffineVolume k L x := by
  classical
  intro w
  let v := (a : L) • originAffineVolume k L x
  have hv : v ∈ omB k L B d := smul_mem_omB a.property hvol
  have hlocModel (e : B →ₐ[k] k) (he : ∀ j, e (r (sel j)) = 0) :
      ∃ f : OriginFibrePoint k L x,
        (∀ a b, Val B e a b ↔ Val B₀ f.1 a b) ∧ loc B e = loc B₀ f.1 ∧
        ∃ u : ι → loc B₀ f.1, (∀ l, (u l : L) = (r l : L)) ∧
          Ideal.span (Set.range fun j => u (sel j)) =
            RingHom.ker (locEval B₀ f.1).toRingHom := by
    obtain ⟨f, hf⟩ := hmodel e he
    exact ⟨f, hf, originColumn_model_of_localValues hL e f hf r sel hsel⟩
  have hK (m : ℤ) (hm : m < (d : ℤ)) :
      (acx (fun _ => omB k L B d) fun j => w (sel j)).Z m ≤
        (acx (fun _ => omB k L B d) fun j => w (sel j)).B m := by
    refine (chartKoszul_exact_and_boundary_of_originModel B (r ∘ sel)
      (OrderEmbedding.id (Fin d)) hL ?_).1 m hm
    intro e he
    obtain ⟨f, _, hR, u, hu, hs⟩ := hlocModel e he
    exact ⟨f, hR, u ∘ sel, fun j => hu (sel j), hs⟩
  refine exists_cocycle_with_selected_component (M := omB k L B d) (w := w) sel
    (fun l j => (Commute.all (r l : L) (r j : L)).map (Algebra.lsmul k k (DR k L)))
    (fun l _ hm => smul_mem_omB (r l).property hm) hK hv ?_
  intro l hl
  refine selectedBoundaryValues_mem_of_local B d r sel (smul_mem_omB (r l).property hv) ?_
  intro e
  by_cases he : ∀ j, e (r (sel j)) = 0
  · obtain ⟨f, hval, hR, u, hu, hspan⟩ := hlocModel e he
    have huE : locEval B₀ f.1 (u l) = e (r l) := by
      have h := (hval _ _).mp (val_chartElement B e (r l))
      exact ((val_iff_loc B₀ f.1 _ _).mp ((hu l).symm ▸ h)).choose_spec
    obtain ⟨ha, haE⟩ := (val_iff_loc B₀ f.1 (a : L) (e a)).mp
      ((hval _ _).mp (val_chartElement B e a))
    let a₀ : loc B₀ f.1 := ⟨a, ha⟩
    have hzero : locEval B₀ f.1 (u l * a₀) = 0 := by
      rw [map_mul, huE, show locEval B₀ f.1 a₀ = e a from haE]
      exact hann e he l hl
    have hw : (fun j => Algebra.lsmul k k (DR k L) (u j : L)) = w :=
      funext fun j => congrArg (Algebra.lsmul k k (DR k L)) (hu j)
    change w l v ∈ selectedBoundaryValues (omB k L (loc B e) d) w sel
    rw [hR, ← hw]
    have h := (hL.mem_selectedBoundaryValues_iff_residue f u sel hspan (u l * a₀)).mpr hzero
    change (u l : L) • ((a : L) • originAffineVolume k L x) ∈ _
    simpa only [Subalgebra.coe_mul, mul_smul, a₀] using h
  · push Not at he
    obtain ⟨j, hj⟩ := he
    let r' := (Subalgebra.inclusion (le_loc B e)) ∘ r
    have hunit : IsUnit (r' (sel j)) := isUnit_loc_of_eval_ne_zero B e _
      ((locEval_inclusion B e (r (sel j))).symm ▸ hj)
    exact le_selectedBoundaryValues_of_unit (loc B e) d r' sel hunit
      (omB_mono (le_loc B e) d (smul_mem_omB (r l).property hv))

end GlobalTheory.WH
