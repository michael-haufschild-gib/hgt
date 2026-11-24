import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginCoordinateBasis
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalExteriorPullback

/-! Differentiating cleared equations in origin coordinates gives a
local matrix whose residue is the given cotangent matrix. -/

noncomputable section

open KaehlerDifferential GlobalTheory.PD GlobalTheory.WH GaloisForLFunctions.HTGeometry

namespace GlobalTheory.PD

section LocalRows

variable {k R : Type} [Field k] [CommRing R] [Algebra k R] {d : ℕ}

private theorem residue_coord_D_of_clearedRow (e : R →ₐ[k] k)
    (b : Module.Basis (Fin d) R Ω[R⁄k]) (t : Fin d → R) (hb : ∀ l, b l = D k R (t l))
    (ht : ∀ l, e (t l) = 0) (c z : R) (hc : e c ≠ 0)
    (g : Fin d → R) (h : c * z = ∑ l, g l * t l) (M : Fin d → k)
    (hM : ∀ l, e (g l) = e c * M l) :
    ∀ l, e (b.repr (D k R z) l) = M l := by
  have hz : e z = 0 := by
    have hz := congrArg e h
    simp only [map_mul, map_sum, ht, mul_zero, Finset.sum_const_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left hc
  intro l
  have hd := congrArg (fun w => e (b.coord l (D k R w))) h
  change e (b.coord l (D k R (c * z))) =
    e (b.coord l (D k R (∑ j, g j * t j))) at hd
  rw [map_sum] at hd
  simp only [Derivation.leibniz, map_add, map_sum, map_smul, smul_eq_mul, map_mul,
    ht, hz, zero_mul, add_zero, ← hb, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply, apply_ite, map_zero,
    mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hd
  change e c * e (b.repr (D k R z) l) = e (g l) at hd
  exact mul_left_cancel₀ hc (hd.trans (hM l))

end LocalRows

section NormalizedRows

variable {k F L : Type} [Field k] [CharZero k] [Field F] [Field L]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  {d : ℕ} {x : Fin (d + 1) → F}

local notation "B" => rB k L x {0}
local notation "t" => fun l : Fin d => algebraMap F L (x (Fin.succ l) / x 0)

/-- The derivatives of the second coordinate list have local
coefficients given at the point by the linear terms of the cleared
coordinate equations. -/
theorem IsFinCover.exists_originDifferentialRows (h : IsFinCover k L x)
    [IsReduced (B ⧸ originIdeal k L x)] (e : OriginFibrePoint k L x)
    (z : Fin d → L) (M : Matrix (Fin d) (Fin d) k)
    (hrow : ∀ m, ∃ (c : B) (g : Fin d → B), e.1 c ≠ 0 ∧
      (c : L) * z m = ∑ l, (g l : L) * t l ∧ ∀ l, e.1 (g l) = e.1 c * M m l) :
    ∃ A : Matrix (Fin d) (Fin d) (loc B e.1),
      A.map (locEval B e.1) = M ∧
      ∀ m, D k L (z m) = ∑ l, (A m l : L) • D k L (t l) := by
  let q : Ideal B := RingHom.ker e.1.toRingHom
  letI : q.IsPrime := (algebraPointKernel_isMaximal e.1).isPrime
  let C := Localization.AtPrime q
  let f : C →ₐ[k] L := localChartEmbedding B e.1
  let v : C →ₐ[k] k := localizedEvaluation B e.1
  let i : B →ₐ[k] C := IsScalarTower.toAlgHom k B C
  let tc (l : Fin d) : C := i ⟨t l, tco_mem k L x l⟩
  have hi (a : B) : f (i a) = (a : L) := localChartEmbedding_algebraMap B e.1 a
  have hv (a : B) : v (i a) = e.1 a := localizedEvaluation_algebraMap B e.1 a
  have htc (l : Fin d) : f (tc l) = t l := hi _
  have htv (l : Fin d) : v (tc l) = 0 := (hv _).trans (e.2 l)
  obtain ⟨b, hb⟩ := h.exists_originCoordinateBasis e
  have hbt (l : Fin d) : b l = D k C (tc l) := hb l
  have hdT (l : Fin d) : algHomKaehlerMap f (b l) = D k L (t l) := by
    rw [hbt, algHomKaehlerMap_D, htc]
  choose c g hc he hM using hrow
  have hex (m : Fin d) : ∃ w : C, f w = z m := by
    have hn : (c m : L) ≠ 0 := by
      intro hz
      exact hc m (by rw [show c m = 0 from Subtype.ext hz, map_zero])
    let a : q.primeCompl := ⟨c m, hc m⟩
    let N := ∑ l, g m l * ⟨t l, tco_mem k L x l⟩
    let w := IsLocalization.mk' C N a
    refine ⟨w, mul_left_cancel₀ hn ?_⟩
    have hw : i (c m) * w = i N := IsLocalization.mk'_spec' C N a
    calc
      _ = f (i (c m) * w) := by rw [map_mul, hi]
      _ = (N : L) := by rw [hw, hi]
      _ = _ := by
        change (B).val N = _
        simpa only [N, map_sum, map_mul, Subalgebra.val_apply] using (he m).symm
  choose w hw using hex
  let ac (m l : Fin d) := b.repr (D k C (w m)) l
  have hav (m l : Fin d) : v (ac m l) = M m l := by
    have hc' : v (i (c m)) ≠ 0 := (hv (c m)).symm ▸ hc m
    have hwc : i (c m) * w m = ∑ l, i (g m l) * tc l := by
      apply localChartEmbedding_injective B e.1
      change f _ = f _
      simpa only [map_mul, map_sum, hi, hw, htc] using he m
    exact residue_coord_D_of_clearedRow v b tc hbt htv _ _ hc' _ hwc _
      (fun l => by simpa only [hv] using hM m l) l
  let A : Matrix (Fin d) (Fin d) (loc B e.1) := fun m l => ⟨f (ac m l), ac m l, rfl⟩
  refine ⟨A, ?_, ?_⟩
  · ext m l
    exact (locEval_localChartEmbedding B e.1 (ac m l)).trans (hav m l)
  · intro m
    have hd := congrArg (algHomKaehlerMap f) (b.sum_repr (D k C (w m)))
    simpa only [map_sum, algHomKaehlerMap_smul, hdT, algHomKaehlerMap_D, hw, A, ac] using hd.symm

end NormalizedRows

end GlobalTheory.PD
