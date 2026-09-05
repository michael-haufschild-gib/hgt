import GaloisForLFunctions.HTGeometry.AutonomousCompJetAll

/-!
# Recovering the inner jets from the outer ones

The leading term of the `j`-th jet of a composition is `(f′∘g)·g⁽ʲ⁾`, everything else involving only
`g`-jets of order below `j`.  Solving for `g⁽ʲ⁾` expresses the inner jet through the outer jets, the
composed jets and the lower inner jets — the backward half of the jet equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- **The composed derivative is nonzero.**  If `f′∘g` vanished identically, `f′` would vanish on a
neighbourhood of `g 0`, hence everywhere, making `f` constant. -/
theorem compJetElem_one_ne_zero {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) :
    compJetElem hf hg 1 ≠ 0 := by
  intro hcon
  rw [compJetElem] at hcon
  have hzero := (analyticMeroElement_eq_zero_iff _).mp hcon
  have hvanish : ∀ z : ℂ, deriv f (g z) = 0 := by
    intro z
    have h := hzero z (Set.mem_univ z)
    simpa [compJetFun, iteratedDeriv_one] using h
  have hgnc : ¬ ∀ᶠ w in nhds (0 : ℂ), g w = g 0 := by
    intro hev
    have hzero' : meromorphicOrderAt (fun w => g w - g 0) 0 = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards [nhdsWithin_le_nhds hev] with x hx
      simp [hx]
    exact meromorphicOrderAt_sub_const_ne_top hg hgnp (g 0) 0 hzero'
  rcases (hg.analyticAt (0 : ℂ)).eventually_constant_or_nhds_le_map_nhds with h | h
  · exact hgnc h
  · have hev : ∀ᶠ v in nhds (g 0), deriv f v = 0 := by
      refine h ?_
      rw [Filter.mem_map]
      filter_upwards with w
      simp [Set.mem_preimage, hvanish w]
    have hfan : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
      hf.differentiableOn.analyticOnNhd isOpen_univ
    have hdan : AnalyticOnNhd ℂ (deriv f) (Set.univ : Set ℂ) := hfan.deriv
    have hevW : ∀ᶠ x in nhdsWithin (g 0) ({g 0}ᶜ : Set ℂ), deriv f x = 0 :=
      hev.filter_mono nhdsWithin_le_nhds
    have hfreq : ∃ᶠ x in nhdsWithin (g 0) ({g 0}ᶜ : Set ℂ), deriv f x = 0 := hevW.frequently
    have hall := hdan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ (g 0)) hfreq
    have hconst : ∀ x y : ℂ, f x = f y :=
      fun x y => is_const_of_deriv_eq_zero hf (fun w => by simpa using hall (Set.mem_univ w)) x y
    exact hfnp ⟨Polynomial.C (f 0), fun z => by simpa using hconst z 0⟩

/-- The graded ring: composed jets of index at most `m+1` and inner jets of index at most `m`. -/
def gradedJetRing {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (m : ℕ) :
    Subalgebra ℂ (meroField (Set.univ : Set ℂ)) :=
  Algebra.adjoin ℂ ((Set.range fun i : Fin (m + 2) => compJetElem hf hg (i : ℕ))
    ∪ (Set.range fun j : Fin m => jetElem hg ((j : ℕ) + 1)))

theorem compJetElem_mem_gradedJetRing {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {m i : ℕ} (hi : i ≤ m + 1) :
    compJetElem hf hg i ∈ gradedJetRing hf hg m :=
  Algebra.subset_adjoin (Or.inl ⟨⟨i, by omega⟩, rfl⟩)

theorem jetElem_mem_gradedJetRing {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {m j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ m) :
    jetElem hg j ∈ gradedJetRing hf hg m := by
  have hj' : j - 1 < m := by omega
  refine Algebra.subset_adjoin (Or.inr ⟨⟨j - 1, hj'⟩, ?_⟩)
  show jetElem hg ((j - 1) + 1) = jetElem hg j
  congr 1
  omega

theorem gradedJetRing_mono {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {m m' : ℕ} (h : m ≤ m') : gradedJetRing hf hg m ≤ gradedJetRing hf hg m' := by
  refine Algebra.adjoin_mono ?_
  rintro y (⟨i, rfl⟩ | ⟨j, rfl⟩)
  · exact Or.inl ⟨⟨(i : ℕ), by omega⟩, rfl⟩
  · exact Or.inr ⟨⟨(j : ℕ), by omega⟩, rfl⟩

/-- **The graded ring absorbs one differentiation.** -/
theorem deriv_mem_gradedJetRing_succ {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (m : ℕ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ gradedJetRing hf hg m) : x′ ∈ gradedJetRing hf hg (m + 1) := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      rcases hy with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · rw [deriv_compJetElem]
        exact Subalgebra.mul_mem _
          (compJetElem_mem_gradedJetRing hf hg (by omega : (i : ℕ) + 1 ≤ m + 2))
          (jetElem_mem_gradedJetRing hf hg (by omega : 1 ≤ 1) (by omega : 1 ≤ m + 1))
      · rw [deriv_jetElem]
        exact jetElem_mem_gradedJetRing hf hg (by omega : 1 ≤ (j : ℕ) + 1 + 1)
          (by omega : (j : ℕ) + 1 + 1 ≤ m + 1)
  | algebraMap c =>
      have hconst : (algebraMap ℂ (meroField (Set.univ : Set ℂ))) c
          = analyticMeroElement (fun _ : ℂ => c) analyticOnNhd_const :=
        (analyticMeroElement_const (Set.univ : Set ℂ) c).trans rfl
      have hderivfun : deriv (fun _ : ℂ => c) = fun _ : ℂ => (0 : ℂ) := by
        funext z
        simp
      rw [hconst, deriv_analyticMeroElement,
        analyticMeroElement_congr _ analyticOnNhd_const hderivfun, analyticMeroElement_zero]
      exact Subalgebra.zero_mem _
  | add a b ha hb iha ihb =>
      rw [deriv_add' a b]
      exact Subalgebra.add_mem _ iha ihb
  | mul a b ha hb iha ihb =>
      rw [deriv_mul' a b]
      exact Subalgebra.add_mem _
        (Subalgebra.mul_mem _ (gradedJetRing_mono hf hg (by omega) ha) ihb)
        (Subalgebra.mul_mem _ (gradedJetRing_mono hf hg (by omega) hb) iha)

/-- **The leading term of a composed jet.**  The `j+1`-st jet of `f ∘ g` is `(f′∘g)·g⁽ʲ⁺¹⁾` up to an
element of the graded ring of level `j`. -/
theorem jetElem_comp_sub_mem_gradedJetRing {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ (fun w => f (g w))) (j : ℕ) :
    jetElem hcomp (j + 1) - compJetElem hf hg 1 * jetElem hg (j + 1)
      ∈ gradedJetRing hf hg j := by
  induction j with
  | zero =>
      have h0 : compJetElem hf hg 0 = jetElem hcomp 0 := compJetElem_zero hf hg hcomp
      have h1 : (compJetElem hf hg 0)′ = compJetElem hf hg 1 * jetElem hg 1 :=
        deriv_compJetElem hf hg 0
      rw [h0] at h1
      have h2 : (jetElem hcomp 0)′ = jetElem hcomp 1 := deriv_jetElem hcomp 0
      rw [h2] at h1
      rw [h1, sub_self]
      exact Subalgebra.zero_mem _
  | succ k ih =>
      set r : meroField (Set.univ : Set ℂ) :=
        jetElem hcomp (k + 1) - compJetElem hf hg 1 * jetElem hg (k + 1) with hr
      have hsplit : jetElem hcomp (k + 1)
          = compJetElem hf hg 1 * jetElem hg (k + 1) + r := by
        rw [hr]
        ring
      have hd : (jetElem hcomp (k + 1))′ = jetElem hcomp (k + 2) := deriv_jetElem hcomp (k + 1)
      have hderiv : jetElem hcomp (k + 2)
          = (compJetElem hf hg 1)′ * jetElem hg (k + 1)
            + compJetElem hf hg 1 * jetElem hg (k + 2) + r′ := by
        rw [← hd, hsplit, deriv_add' _ r, deriv_mul' (compJetElem hf hg 1) (jetElem hg (k + 1)),
          deriv_jetElem hg (k + 1)]
        ring
      have ha' : (compJetElem hf hg 1)′ = compJetElem hf hg 2 * jetElem hg 1 :=
        deriv_compJetElem hf hg 1
      rw [hderiv, ha']
      have hsub : compJetElem hf hg 2 * jetElem hg 1 * jetElem hg (k + 1)
          + compJetElem hf hg 1 * jetElem hg (k + 2) + r′
          - compJetElem hf hg 1 * jetElem hg (k + 2)
          = compJetElem hf hg 2 * jetElem hg 1 * jetElem hg (k + 1) + r′ := by
        ring
      rw [hsub]
      refine Subalgebra.add_mem _ ?_ (deriv_mem_gradedJetRing_succ hf hg k ih)
      exact Subalgebra.mul_mem _
        (Subalgebra.mul_mem _ (compJetElem_mem_gradedJetRing hf hg (by omega : 2 ≤ k + 2))
          (jetElem_mem_gradedJetRing hf hg (by omega : 1 ≤ 1) (by omega : 1 ≤ k + 1)))
        (jetElem_mem_gradedJetRing hf hg (by omega : 1 ≤ k + 1) (by omega : k + 1 ≤ k + 1))

/-- **The outer jets lie in the graded ring.**  The `k`-th jet of `f ∘ g` lies in the ring generated
by the composed jets of index at most `k+1` and the inner jets of index `1` to `k`; the inner
function itself is never needed. -/
theorem jetElem_comp_mem_gradedJetRing {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hcomp : Differentiable ℂ (fun w => f (g w))) (k : ℕ) :
    jetElem hcomp k ∈ gradedJetRing hf hg k := by
  induction k with
  | zero =>
      rw [← compJetElem_zero hf hg hcomp]
      exact compJetElem_mem_gradedJetRing hf hg (by omega : 0 ≤ 0 + 1)
  | succ m ih =>
      have hd : (jetElem hcomp m)′ = jetElem hcomp (m + 1) := deriv_jetElem hcomp m
      rw [← hd]
      exact deriv_mem_gradedJetRing_succ hf hg m ih

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The inner jets are algebraic over the outer jet field.**  Solving the leading-term identity for
`g⁽ʲ⁾` expresses it through the outer jets and the composed jets, all algebraic over the field the
outer jets generate. -/
theorem isAlgebraic_jetElem_over_compJets {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (haut : AutonomousFirstOrder f)
    (hcomp : Differentiable ℂ (fun w => f (g w)))
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z)
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c)
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (n : ℕ) :
    ∀ j : ℕ, 1 ≤ j → j ≤ n →
      IsAlgebraic ↥(IntermediateField.adjoin ℂ
        (Set.range fun k : Fin (n + 1) => jetElem hcomp (k : ℕ))) (jetElem hg j) := by
  classical
  set K : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ (Set.range fun k : Fin (n + 1) => jetElem hcomp (k : ℕ)) with hK
  set M := algebraicClosure ↥K (meroField (Set.univ : Set ℂ)) with hM
  have hKmem : ∀ y : meroField (Set.univ : Set ℂ), y ∈ K → y ∈ M := by
    intro y hy
    exact IntermediateField.algebraMap_mem M (⟨y, hy⟩ : ↥K)
  have hhjetK : ∀ k : ℕ, k ≤ n → jetElem hcomp k ∈ K := by
    intro k hk
    rw [hK]
    exact IntermediateField.subset_adjoin ℂ _ ⟨⟨k, by omega⟩, rfl⟩
  -- the composed jets are algebraic over `K`
  have hbase : IntermediateField.adjoin ℂ ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ)))
      ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y rfl
    exact hhjetK 0 (by omega)
  letI : Algebra ↥(IntermediateField.adjoin ℂ
      ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ)))) ↥K :=
    (IntermediateField.inclusion hbase).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(IntermediateField.adjoin ℂ
      ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ)))) ↥K
      (meroField (Set.univ : Set ℂ)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcompM : ∀ i : ℕ, compJetElem hf hg i ∈ M := by
    intro i
    have halg := isAlgebraic_compJetElem_of_autonomous hf hg haut hcomp hncomp hncg i
    exact mem_algebraicClosure_iff.mpr (halg.tower_top ↥K)
  -- the inner jets, by strong induction
  have hjetM : ∀ j : ℕ, 1 ≤ j → j ≤ n → jetElem hg j ∈ M := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
        intro hj1 hjn
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hfil := jetElem_comp_sub_mem_gradedJetRing hf hg hcomp k
        set r : meroField (Set.univ : Set ℂ) :=
          jetElem hcomp (k + 1) - compJetElem hf hg 1 * jetElem hg (k + 1) with hr
        -- the graded ring sits inside `M`
        have hgen : ∀ y ∈ ((Set.range fun i : Fin (k + 2) => compJetElem hf hg (i : ℕ))
            ∪ (Set.range fun jj : Fin k => jetElem hg ((jj : ℕ) + 1))), y ∈ M := by
          rintro y (⟨i, rfl⟩ | ⟨jj, rfl⟩)
          · exact hcompM _
          · exact ih ((jj : ℕ) + 1) (by omega) (by omega) (by omega)
        have hrM : r ∈ M := by
          have hsub : gradedJetRing hf hg k ≤ M.toSubalgebra.restrictScalars ℂ := by
            refine Algebra.adjoin_le ?_
            intro y hy
            exact hgen y hy
          exact hsub hfil
        have haM : compJetElem hf hg 1 ∈ M := hcompM 1
        have hane : compJetElem hf hg 1 ≠ 0 := compJetElem_one_ne_zero hf hg hfnp hgnp
        have hhM : jetElem hcomp (k + 1) ∈ M := hKmem _ (hhjetK (k + 1) hjn)
        have hsolve : jetElem hg (k + 1)
            = (jetElem hcomp (k + 1) - r) * (compJetElem hf hg 1)⁻¹ := by
          have hd : jetElem hcomp (k + 1) - r = compJetElem hf hg 1 * jetElem hg (k + 1) := by
            rw [hr]
            ring
          rw [hd, mul_comm, ← mul_assoc, inv_mul_cancel₀ hane, one_mul]
        rw [hsolve]
        exact Subalgebra.mul_mem _ (Subalgebra.sub_mem _ hhM hrM)
          (IntermediateField.inv_mem M haM)
  intro j hj1 hjn
  exact mem_algebraicClosure_iff.mp (hjetM j hj1 hjn)

end

end GaloisForLFunctions.HTGeometry
