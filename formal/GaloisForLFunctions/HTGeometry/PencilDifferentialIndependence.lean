import GaloisForLFunctions.HTGeometry.DirectionalIterateJet
import GaloisForLFunctions.HTGeometry.PencilLineRestriction
import GaloisForLFunctions.HTGeometry.SeveralVariableTranslation
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# From joint directional hypertranscendence to differential independence

An entire function on `ℂ^d` is an element of the several-variable meromorphic field, its differential
jets for the directional derivation are the iterated directional derivatives, and a polynomial in
those jets evaluates to the germ of the corresponding function.  So a family with no algebraic
differential relation over `ℂ(z₁,…,z_d)` is differentially independent over `ℂ` in that field — the
input the localized Stanley--Reisner matroid rank law consumes.
-/

open Filter Topology Set Function MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open Bottcher GaloisForLFunctions

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The analytic germ of an entire function. -/
def entireGermGen (f : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) :
    analyticSubringGen (Set.univ : Set E) :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) f, ⟨f, hf, rfl⟩⟩

@[simp] theorem entireGermGen_coe (f : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) :
    (entireGermGen f hf : Germ (𝓟 (Set.univ : Set E)) ℂ) = (f : Germ (𝓟 (Set.univ : Set E)) ℂ) :=
  rfl

theorem entireGermGen_eq_zero_iff (f : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) :
    entireGermGen f hf = 0 ↔ ∀ z : E, f z = 0 := by
  constructor
  · intro h z
    have hval := congrArg (fun a : analyticSubringGen (Set.univ : Set E) =>
      (a : Germ (𝓟 (Set.univ : Set E)) ℂ)) h
    rw [entireGermGen_coe, ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq] at hval
    exact eventually_principal.mp hval z (Set.mem_univ z)
  · intro h
    apply Subtype.ext
    rw [entireGermGen_coe, ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq]
    exact eventually_principal.mpr fun z _ => h z

theorem entireGermGen_add (f g : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) :
    entireGermGen (fun z => f z + g z) (hf.add hg) = entireGermGen f hf + entireGermGen g hg := by
  apply Subtype.ext
  rfl

theorem entireGermGen_mul (f g : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) :
    entireGermGen (fun z => f z * g z) (hf.mul hg) = entireGermGen f hf * entireGermGen g hg := by
  apply Subtype.ext
  rfl

theorem entireGermGen_const (a : ℂ) :
    entireGermGen (fun _ : E => a) analyticOnNhd_const =
      constToAnalyticGen (Set.univ : Set E) a := rfl

theorem analyticSubringGenDirDeriv_entireGermGen (w : E) (f : E → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) :
    analyticSubringGenDirDeriv w (isOpen_univ (X := E)) (entireGermGen f hf) =
      entireGermGen (dirDerivFun w f) (analyticOnNhd_dirDerivFun w hf) := by
  apply Subtype.ext
  rfl

theorem analyticSubringGenDirDeriv_const (w : E) (a : ℂ) :
    analyticSubringGenDirDeriv w (isOpen_univ (X := E))
      (constToAnalyticGen (Set.univ : Set E) a) = 0 := by
  rw [← entireGermGen_const, analyticSubringGenDirDeriv_entireGermGen]
  rw [entireGermGen_eq_zero_iff]
  intro z
  rw [dirDerivFun]
  simp

/-! ### The differential field of entire germs -/

instance genDomain : IsDomain (analyticSubringGen (Set.univ : Set E)) :=
  isDomain_analyticSubringGen Set.univ isOpen_univ isPreconnected_univ_gen Set.univ_nonempty

instance genAnalyticAlgebra : Algebra ℂ (analyticSubringGen (Set.univ : Set E)) :=
  (constToAnalyticGen (Set.univ : Set E)).toAlgebra

/-- Iterated directional derivatives of an entire function are entire. -/
theorem analyticOnNhd_dirDerivFun_iterate (w : E) {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (r : ℕ) :
    AnalyticOnNhd ℂ ((dirDerivFun w)^[r] f) Set.univ := by
  induction r generalizing f with
  | zero => simpa using hf
  | succ r ih =>
      rw [Function.iterate_succ_apply]
      exact ih (analyticOnNhd_dirDerivFun w hf)

/-- **The differential jets of an entire germ are its iterated directional derivatives.** -/
theorem differentialJet_entireGermGen (w : E) (f : E → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (r : ℕ) :
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
      Set.univ_nonempty
    differentialJet r
        (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
          (entireGermGen f hf)) =
      algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
        (entireGermGen ((dirDerivFun w)^[r] f) (analyticOnNhd_dirDerivFun_iterate w hf r)) := by
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
    Set.univ_nonempty
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
      rw [differentialJet_succ, ih f hf,
        meroFieldGenDirDifferential_algebraMap w (isOpen_univ (X := E)) isPreconnected_univ_gen
          Set.univ_nonempty, analyticSubringGenDirDeriv_entireGermGen]
      congr 1
      apply Subtype.ext
      have hfun : dirDerivFun w ((dirDerivFun w)^[r] f) = (dirDerivFun w)^[r + 1] f :=
        (Function.iterate_succ_apply' (dirDerivFun w) r f).symm
      rw [entireGermGen_coe, entireGermGen_coe, hfun]

/-- **A polynomial in entire germs is the germ of the corresponding function.** -/
theorem exists_entireGermGen_aeval {ι : Type} (g : ι → E → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) Set.univ) (Q : MvPolynomial ι ℂ) :
    ∃ (F : E → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ),
      MvPolynomial.aeval (fun i => entireGermGen (g i) (hg i)) Q = entireGermGen F hF ∧
        ∀ z, F z = MvPolynomial.eval (fun i => g i z) Q := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a =>
      refine ⟨fun _ => a, analyticOnNhd_const, ?_, fun z => by simp⟩
      rw [MvPolynomial.aeval_C, entireGermGen_const]
      rfl
  | add p q hp hq =>
      obtain ⟨Fp, hFp, hpe, hpv⟩ := hp
      obtain ⟨Fq, hFq, hqe, hqv⟩ := hq
      refine ⟨fun z => Fp z + Fq z, hFp.add hFq, ?_, fun z => by simp [hpv z, hqv z]⟩
      rw [map_add, hpe, hqe, entireGermGen_add]
  | mul_X p i hp =>
      obtain ⟨Fp, hFp, hpe, hpv⟩ := hp
      refine ⟨fun z => Fp z * g i z, hFp.mul (hg i), ?_, fun z => by simp [hpv z]⟩
      rw [map_mul, hpe, MvPolynomial.aeval_X, entireGermGen_mul]


/-! ### The bridge -/

set_option maxHeartbeats 1000000 in
/-- **Joint directional hypertranscendence gives differential independence over `ℂ`.** -/
theorem differentialIndependent_of_jointlyDirHypertranscendental {d : ℕ} {ι : Type}
    (w : Fin d → ℂ) (f : ι → (Fin d → ℂ) → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) Set.univ)
    (h : JointlyDirHypertranscendental w f) :
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
      isPreconnected_univ_gen Set.univ_nonempty
    DifferentialIndependent ℂ
      (fun i => algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
        (meroFieldGen (Set.univ : Set (Fin d → ℂ))) (entireGermGen (f i) (hf i))) := by
  classical
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
    isPreconnected_univ_gen Set.univ_nonempty
  rw [DifferentialIndependent, algebraicIndependent_iff]
  intro Q hQ
  by_contra hQne
  set g : ι × ℕ → (Fin d → ℂ) → ℂ := fun p => (dirDerivFun w)^[p.2] (f p.1) with hgdef
  have hgA : ∀ p, AnalyticOnNhd ℂ (g p) Set.univ :=
    fun p => analyticOnNhd_dirDerivFun_iterate w (hf p.1) p.2
  have hjetfun :
      (fun p : ι × ℕ => differentialJet p.2
          (algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
            (meroFieldGen (Set.univ : Set (Fin d → ℂ))) (entireGermGen (f p.1) (hf p.1))))
        = fun p : ι × ℕ =>
          algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
            (meroFieldGen (Set.univ : Set (Fin d → ℂ))) (entireGermGen (g p) (hgA p)) := by
    funext p
    rw [differentialJet_entireGermGen w (f p.1) (hf p.1) p.2]
  rw [hjetfun] at hQ
  obtain ⟨F, hF, hFeq, hFval⟩ := exists_entireGermGen_aeval g hgA Q
  have hmap : MvPolynomial.aeval
      (fun p : ι × ℕ => algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
        (meroFieldGen (Set.univ : Set (Fin d → ℂ))) (entireGermGen (g p) (hgA p))) Q =
      algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
        (meroFieldGen (Set.univ : Set (Fin d → ℂ)))
        (MvPolynomial.aeval (fun p : ι × ℕ => entireGermGen (g p) (hgA p)) Q) := by
    exact (MvPolynomial.comp_aeval_apply _
      (IsScalarTower.toAlgHom ℂ (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
        (meroFieldGen (Set.univ : Set (Fin d → ℂ)))) Q).symm
  rw [hmap, hFeq] at hQ
  have hinj : Function.Injective
      (algebraMap (analyticSubringGen (Set.univ : Set (Fin d → ℂ)))
        (meroFieldGen (Set.univ : Set (Fin d → ℂ)))) :=
    IsFractionRing.injective _ _
  have hFzero : entireGermGen F hF = 0 := hinj (by rw [hQ, map_zero])
  have hFvanish : ∀ z, F z = 0 := (entireGermGen_eq_zero_iff F hF).mp hFzero
  -- transport the relation to the several-variable form
  set n : ℕ := Q.vars.sup fun p : ι × ℕ => p.2 with hn
  have hρinj : Function.Injective (fun p : ι × Fin (n + 1) => (p.1, (p.2 : ℕ))) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    rw [Prod.mk.injEq] at hab
    exact Prod.ext hab.1 (Fin.ext hab.2)
  have hvars : (Q.vars : Set (ι × ℕ)) ⊆
      Set.range fun p : ι × Fin (n + 1) => (p.1, (p.2 : ℕ)) := by
    intro q hq
    have hle : q.2 ≤ n := Finset.le_sup (f := fun r : ι × ℕ => r.2) hq
    exact ⟨(q.1, ⟨q.2, by omega⟩), rfl⟩
  obtain ⟨Q₀, hQ₀⟩ :=
    MvPolynomial.exists_rename_eq_of_vars_subset_range Q _ hρinj hvars
  have hQ₀ne : Q₀ ≠ 0 := by
    intro hzero
    exact hQne (by rw [← hQ₀, hzero, map_zero])
  refine h ⟨n, MvPolynomial.rename (Sum.inr : ι × Fin (n + 1) → (Fin d) ⊕ (ι × Fin (n + 1))) Q₀,
    ?_, fun z => ?_⟩
  · intro hzero
    exact hQ₀ne (MvPolynomial.rename_injective _ (Sum.inr_injective) (by rw [hzero, map_zero]))
  · rw [MvPolynomial.eval_rename]
    have hcomp : (dirJetPoint w f n z) ∘ (Sum.inr : ι × Fin (n + 1) → (Fin d) ⊕ (ι × Fin (n + 1)))
        = fun p : ι × Fin (n + 1) => g (p.1, (p.2 : ℕ)) z := by
      funext p
      show iteratedDeriv (p.2 : ℕ) (fun s : ℂ => f p.1 (z + s • w)) 0 = g (p.1, (p.2 : ℕ)) z
      rw [hgdef]
      exact (dirDerivFun_iterate_eq_iteratedDeriv w (p.2 : ℕ) (hf p.1) z).symm
    rw [hcomp]
    have hback : MvPolynomial.eval (fun p : ι × Fin (n + 1) => g (p.1, (p.2 : ℕ)) z) Q₀ =
        MvPolynomial.eval (fun p : ι × ℕ => g p z) Q := by
      rw [← hQ₀, MvPolynomial.eval_rename]
      rfl
    rw [hback, ← hFval z, hFvanish z]


end

end GaloisForLFunctions.HTGeometry
