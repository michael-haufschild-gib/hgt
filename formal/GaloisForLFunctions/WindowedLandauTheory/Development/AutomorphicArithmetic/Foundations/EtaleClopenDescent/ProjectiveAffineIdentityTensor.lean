import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TraceWedgeDuality
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplementaryTraceDuality
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFormDualFamily

/-! On one normalized projective chart, the identity on rational forms
has a tensor representative consisting of regular complementary forms. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology KaehlerDifferential
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p q : ℕ}

/-- The left wedge factor acts on the complementary right factor
by the trace of the top coefficient. -/
def traceWedgeLeftDual (τ : DR k E →ₗ[E] E) :
    ExteriorDifferentials k E q →ₗ[F] Module.Dual F (ExteriorDifferentials k E p) :=
  (traceWedgeDual (p := q) (q := p) τ).flip

omit [CharZero k] [Algebra k F] [IsScalarTower k F E] in
theorem traceWedgeLeftDual_apply (τ : DR k E →ₗ[E] E)
    (b : ExteriorDifferentials k E q) (a : ExteriorDifferentials k E p) :
    traceWedgeLeftDual (F := F) τ b a = Algebra.trace F E (τ ((b : DR k E) * (a : DR k E))) := rfl

theorem IsFinCover.traceWedgeLeftDual_surjective (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d) :
    Function.Surjective (traceWedgeLeftDual (F := F) (p := p) (q := q) τ) := by
  intro ψ
  obtain ⟨b, hb⟩ := (h.traceWedgeDual_bijective τ hτ hpq).2 ψ
  let e : F := (-1 : F) ^ (p * q)
  refine ⟨e • b, LinearMap.ext fun a => ?_⟩
  have hba : (b : DR k E) * (a : DR k E) =
      algebraMap F E e • ((a : DR k E) * (b : DR k E)) := by
    simpa only [e, map_pow, map_neg, map_one, Nat.mul_comm q p] using
      GaloisForLFunctions.HTGeometry.exteriorPower_mul_comm b a
  have he : e * e = 1 := by
    change (-1 : F) ^ (p * q) * (-1 : F) ^ (p * q) = 1
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  rw [traceWedgeLeftDual_apply]
  change Algebra.trace F E (τ ((algebraMap F E e • (b : DR k E)) * (a : DR k E))) = ψ a
  rw [smul_mul_assoc, hba, smul_smul, ← map_mul, he, map_one, one_smul]
  exact LinearMap.congr_fun hb a

/-- The diagonal tensor of a normalized chart, contracted against a
rational form, gives that form times the affine volume coefficient. -/
theorem IsFinCover.exists_affineIdentityFamily (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d)
    (i : Fin (d + 1)) :
    ∃ (n : ℕ) (u : Fin n → ExteriorDifferentials k E q) (v : Fin n → ExteriorDifferentials k E p),
      (∀ j, u j ∈ regularExteriorLattice (rB k E x {i}) q) ∧
      (∀ j, v j ∈ regularExteriorLattice (rB k E x {i}) p) ∧
      ∀ a : ExteriorDifferentials k E p,
        (∑ j, traceWedgeLeftDual (F := F) τ (u j) a • v j) = (∏ j, x j / x i) • a := by
  obtain ⟨n, v, φ, hv, hφ, hsum⟩ := h.exists_formDualFamily_chart i p
  let c : F := ∏ j, x j / x i
  let f : F := ∏ j, x i / x j
  have hfc : f * c = 1 := by
    change (∏ j, x i / x j) * (∏ j, x j / x i) = 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => by
      rw [div_mul_div_cancel₀ (h.pd.ne j), div_self (h.pd.ne i)]
  have hex (j : Fin n) :=
    h.traceWedgeLeftDual_surjective τ hτ hpq (c • φ j)
  choose w hw using hex
  have hw' (j : Fin n) : (w j : DR k E) ∈ omB k E (rB k E x {i}) q := by
    refine (h.complementary_trace_dual_iff τ hτ (Finset.mem_singleton_self i) hpq (w j)).mp ?_
    intro a ha
    let a' : ExteriorDifferentials k E p := ⟨a, omB_le_degree (B := rB k E x {i}) (p := p) ha⟩
    let e : F := (-1 : F) ^ (p * q)
    have he : e ∈ rA k x {i} := by
      rw [show e = algebraMap k F ((-1 : k) ^ (p * q)) by simp [e]]
      exact Subalgebra.algebraMap_mem _ _
    have hsymm : a * (w j : DR k E) =
        algebraMap F E e • ((w j : DR k E) * a) := by
      simpa only [e, map_pow, map_neg, map_one, a'] using
        GaloisForLFunctions.HTGeometry.exteriorPower_mul_comm a' (w j)
    have htrace := LinearMap.congr_fun (hw j) a'
    rw [traceWedgeLeftDual_apply, LinearMap.smul_apply, smul_eq_mul] at htrace
    change f * Algebra.trace F E (τ (a * (w j : DR k E))) ∈ _
    rw [hsymm, map_smul, IsScalarTower.algebraMap_smul E, map_smul, smul_eq_mul, htrace]
    rw [show f * (e * (c * φ j a')) = e * φ j a' by rw [mul_left_comm f, ← mul_assoc f, hfc, one_mul]]
    exact mul_mem he (hφ j a' ha)
  refine ⟨n, w, v, hw', hv, ?_⟩
  intro a
  conv_rhs => rw [hsum a, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.congr_fun (hw j) a, LinearMap.smul_apply, smul_eq_mul]
  exact (smul_smul c (φ j a) (v j)).symm

end GlobalTheory.PD
