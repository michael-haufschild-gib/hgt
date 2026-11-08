import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockEmbeddings

/-!
# Orthogonal arithmetic core projections on the original complex

Projecting the transformed face basis onto one large-prime core preserves
its exact cutoff and commutes with the original prime-valued boundary.
These projections are natural in height and form pairwise orthogonal
idempotent chain endomorphisms. Every chain is the sum of the projections
on its finite core support, giving an actual decomposition of the complex.
-/

noncomputable section
open scoped Classical
open RHTower CategoryTheory
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- Keep exactly the transformed faces with one fixed large-prime core. -/
def twoPrimeCoreProjection (k : ℕ) (c : TwoPrimeCoreFace) :
    PrimeChainSpace R k →ₗ[R] PrimeChainSpace R k :=
  (Finsupp.linearCombination R (fun s : Set.powersetCard Nat.Primes k =>
    if twoPrimeFaceCore s.val = c then primeTwoPrimeBasis R k s else 0)).comp
      (primeTwoPrimeBasis R k).repr.toLinearMap

theorem twoPrimeCoreProjection_basis (k : ℕ) (c : TwoPrimeCoreFace)
    (s : Set.powersetCard Nat.Primes k) :
    twoPrimeCoreProjection R k c (primeTwoPrimeBasis R k s) =
      if twoPrimeFaceCore s.val = c then primeTwoPrimeBasis R k s else 0 := by
  simp only [twoPrimeCoreProjection,LinearMap.comp_apply,LinearEquiv.coe_coe,
    Module.Basis.repr_self,Finsupp.linearCombination_single,one_smul]

/-- Projecting to a core preserves the original arithmetic cutoff. -/
theorem twoPrimeCoreProjection_cutoff (k N : ℕ) (c : TwoPrimeCoreFace) :
    primeChainCutoff R k N ≤ (primeChainCutoff R k N).comap (twoPrimeCoreProjection R k c) := by
  rw [primeChainCutoff_eq_span_twoPrimeBasis]
  apply Submodule.span_le.mpr
  rintro x ⟨s,hs,rfl⟩
  change twoPrimeCoreProjection R k c (primeTwoPrimeBasis R k s) ∈
    Submodule.span R (primeTwoPrimeBasis R k '' {s | primeFaceProduct s ≤ N})
  rw [twoPrimeCoreProjection_basis]
  split_ifs
  · exact Submodule.subset_span ⟨s,hs,rfl⟩
  · exact Submodule.zero_mem _

/-- The cutoff core projection acts on actual chains, rather than only their coordinates. -/
def twoPrimeCoreCutoffProjection (k N : ℕ) (c : TwoPrimeCoreFace) :
    primeChainCutoff R k N →ₗ[R] primeChainCutoff R k N :=
  (twoPrimeCoreProjection R k c).restrict (fun _ hx => twoPrimeCoreProjection_cutoff R k N c hx)

/-- Each core projection is idempotent. -/
theorem twoPrimeCoreProjection_idempotent (k : ℕ) (c : TwoPrimeCoreFace) :
    (twoPrimeCoreProjection R k c).comp (twoPrimeCoreProjection R k c) =
      twoPrimeCoreProjection R k c := by
  apply (primeTwoPrimeBasis R k).ext
  intro s
  simp only [LinearMap.comp_apply,twoPrimeCoreProjection_basis]
  split_ifs
  · exact twoPrimeCoreProjection_basis R k c s |>.trans (if_pos ‹_›)
  · exact map_zero _

/-- Distinct large-prime cores have disjoint coordinate projections. -/
theorem twoPrimeCoreProjection_orthogonal (k : ℕ) (c d : TwoPrimeCoreFace) (h : c ≠ d) :
    (twoPrimeCoreProjection R k c).comp (twoPrimeCoreProjection R k d) = 0 := by
  apply (primeTwoPrimeBasis R k).ext
  intro s
  simp only [LinearMap.comp_apply,LinearMap.zero_apply,twoPrimeCoreProjection_basis]
  by_cases hd : twoPrimeFaceCore s.val = d
  · rw [if_pos hd,twoPrimeCoreProjection_basis,if_neg (by intro hc; exact h (hc.symm.trans hd))]
  · rw [if_neg hd,map_zero]

/-- Every tagged vector is an eigenvector for its core projection. -/
theorem twoPrimeCoreProjection_vector (c d : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) :
    twoPrimeCoreProjection R (c.val.card+t.degree) d (twoPrimeBlockVector R c t) =
      if c=d then twoPrimeBlockVector R c t else 0 := by
  rw [twoPrimeBlockVector,twoPrimeCoreProjection_basis,twoPrimeFaceCore_tagged]

private theorem scalar_intertwining {V W : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (d : V →ₗ[R] W) (P : V →ₗ[R] V) (Q : W →ₗ[R] W)
    (v : V) (w : W) (a : R) (h : Prop) [Decidable h]
    (hd : d v=a • w) (hp : P v=if h then v else 0) (hq : Q w=if h then w else 0) :
    d (P v)=Q (d v) := by
  rw [hp,hd,map_smul,hq]
  by_cases hh : h
  · simp only [if_pos hh,hd]
  · simp only [if_neg hh,map_zero,smul_zero]

private theorem top_intertwining {V W : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (d : V →ₗ[R] W) (P : V →ₗ[R] V) (Q : W →ₗ[R] W)
    (v : V) (w₂ w₃ : W) (h : Prop) [Decidable h]
    (hd : d v=(2 : R) • w₃-(3 : R) • w₂) (hp : P v=if h then v else 0)
    (hq₂ : Q w₂=if h then w₂ else 0) (hq₃ : Q w₃=if h then w₃ else 0) :
    d (P v)=Q (d v) := by
  rw [hp,hd,map_sub,map_smul,map_smul,hq₂,hq₃]
  by_cases hh : h
  · simp only [if_pos hh,hd]
  · simp only [if_neg hh,map_zero,smul_zero,sub_zero]

/-- The actual prime-valued boundary preserves every large-prime core summand. -/
theorem twoPrimeCoreProjection_boundary (k : ℕ) (c₀ : TwoPrimeCoreFace) :
    (primeValueBoundary R k).comp (twoPrimeCoreProjection R (k+1) c₀) =
      (twoPrimeCoreProjection R k c₀).comp (primeValueBoundary R k) := by
  apply (primeTwoPrimeBasis R (k+1)).ext
  intro s
  simp only [LinearMap.comp_apply]
  generalize hc : twoPrimeFaceCore s.val = c
  generalize ht : twoPrimeFaceTag s.val = t
  have hk := twoPrimeFaceCore_card s.val
  rw [hc,ht,s.property] at hk
  have hs := twoPrimeTaggedFace_recover s.val
  rw [hc,ht] at hs
  cases t with
  | base =>
    have hd : primeValueBoundary R k (primeTwoPrimeBasis R (k+1) s)=0 := by
      rw [primeTwoPrimeBasis_eq_atom]
      apply primeTwoPrimeAtom_boundary_zero
      intro i
      apply twoPrimeCore_gt_three c _
      change c.val = s.val at hs
      rw [hs]
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨i,rfl⟩
    rw [twoPrimeCoreProjection_basis,hc,hd,map_zero]
    by_cases he : c=c₀
    · rw [if_pos he,hd]
    · rw [if_neg he,map_zero]
  | two =>
    have he : c.val.card=k := by change c.val.card+1=k+1 at hk; omega
    subst k
    have hf : s = ⟨twoPrimeTaggedFace c .two,twoPrimeTaggedFace_card c .two⟩ := Subtype.ext hs.symm
    rw [hf]
    change primeValueBoundary R c.val.card
        (twoPrimeCoreProjection R (c.val.card+1) c₀ (twoPrimeTwoVector R c)) =
      twoPrimeCoreProjection R c.val.card c₀ (primeValueBoundary R c.val.card (twoPrimeTwoVector R c))
    exact scalar_intertwining R (primeValueBoundary R c.val.card)
      (twoPrimeCoreProjection R (c.val.card+1) c₀) (twoPrimeCoreProjection R c.val.card c₀)
      (twoPrimeTwoVector R c) (twoPrimeBaseVector R c) 2 (c=c₀)
      (twoPrimeBlockVector_boundary_two R c)
      (twoPrimeCoreProjection_vector R c c₀ .two) (twoPrimeCoreProjection_vector R c c₀ .base)
  | three =>
    have he : c.val.card=k := by change c.val.card+1=k+1 at hk; omega
    subst k
    have hf : s = ⟨twoPrimeTaggedFace c .three,twoPrimeTaggedFace_card c .three⟩ := Subtype.ext hs.symm
    rw [hf]
    change primeValueBoundary R c.val.card
        (twoPrimeCoreProjection R (c.val.card+1) c₀ (twoPrimeThreeVector R c)) =
      twoPrimeCoreProjection R c.val.card c₀ (primeValueBoundary R c.val.card (twoPrimeThreeVector R c))
    exact scalar_intertwining R (primeValueBoundary R c.val.card)
      (twoPrimeCoreProjection R (c.val.card+1) c₀) (twoPrimeCoreProjection R c.val.card c₀)
      (twoPrimeThreeVector R c) (twoPrimeBaseVector R c) 3 (c=c₀)
      (twoPrimeBlockVector_boundary_three R c)
      (twoPrimeCoreProjection_vector R c c₀ .three) (twoPrimeCoreProjection_vector R c c₀ .base)
  | both =>
    have he : k=c.val.card+1 := by change c.val.card+2=k+1 at hk; omega
    subst k
    have hf : s = ⟨twoPrimeTaggedFace c .both,twoPrimeTaggedFace_card c .both⟩ := Subtype.ext hs.symm
    rw [hf]
    change primeValueBoundary R (c.val.card+1)
        (twoPrimeCoreProjection R (c.val.card+2) c₀ (twoPrimeTopVector R c)) =
      twoPrimeCoreProjection R (c.val.card+1) c₀ (primeValueBoundary R (c.val.card+1) (twoPrimeTopVector R c))
    exact top_intertwining R (primeValueBoundary R (c.val.card+1))
      (twoPrimeCoreProjection R (c.val.card+2) c₀) (twoPrimeCoreProjection R (c.val.card+1) c₀)
      (twoPrimeTopVector R c) (twoPrimeTwoVector R c) (twoPrimeThreeVector R c) (c=c₀)
      (twoPrimeBlockVector_boundary_both R c)
      (twoPrimeCoreProjection_vector R c c₀ .both)
      (twoPrimeCoreProjection_vector R c c₀ .two) (twoPrimeCoreProjection_vector R c c₀ .three)

/-- The finite collection of large-prime cores present in a chain. -/
def twoPrimeCoreSupport (k : ℕ) (x : PrimeChainSpace R k) : Finset TwoPrimeCoreFace :=
  ((primeTwoPrimeBasis R k).repr x).support.image (fun s => twoPrimeFaceCore s.val)

/-- Summing the core projections recovers every original chain exactly. -/
theorem twoPrimeCoreProjection_sum (k : ℕ) (x : PrimeChainSpace R k) :
    ∑ c ∈ twoPrimeCoreSupport R k x, twoPrimeCoreProjection R k c x = x := by
  have hx : x ∈ Submodule.span R (primeTwoPrimeBasis R k ''
      {s | twoPrimeFaceCore s.val ∈ twoPrimeCoreSupport R k x}) := by
    rw [Module.Basis.mem_span_image]
    intro s hs
    exact Finset.mem_image_of_mem (fun s => twoPrimeFaceCore s.val) hs
  generalize hS : twoPrimeCoreSupport R k x = S at hx ⊢
  clear hS
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s,hs,rfl⟩ := hy
    calc
      ∑ c ∈ S, twoPrimeCoreProjection R k c (primeTwoPrimeBasis R k s) =
          twoPrimeCoreProjection R k (twoPrimeFaceCore s.val) (primeTwoPrimeBasis R k s) := by
        apply Finset.sum_eq_single
        · intro c hc hne
          rw [twoPrimeCoreProjection_basis,if_neg (Ne.symm hne)]
        · intro hn
          exact False.elim (hn hs)
      _ = primeTwoPrimeBasis R k s := by rw [twoPrimeCoreProjection_basis,if_pos rfl]
  | zero => simp only [map_zero,Finset.sum_const_zero]
  | add y z hy hz ihy ihz => simp only [map_add,Finset.sum_add_distrib,ihy,ihz]
  | smul a y hy ih => simp only [map_smul,← Finset.smul_sum,ih]

/-- The large-prime core projection is an endomorphism of the original cutoff complex. -/
def twoPrimeCoreChainProjection (c : TwoPrimeCoreFace) (N : ℕ) :
    primeCutoffComplex R (primeValueFunctional R) N ⟶
      primeCutoffComplex R (primeValueFunctional R) N :=
  ChainComplex.ofHom
    (fun k => ModuleCat.ofHom (twoPrimeCoreCutoffProjection R k N c))
    (fun k => by
      simp only [primeCutoffComplex,ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (twoPrimeCoreProjection_boundary R k c) x.val)

/-- Core projection commutes with every actual height inclusion. -/
def twoPrimeCoreChainProjectionNat (c : TwoPrimeCoreFace) :
    primeCutoffPersistence R (primeValueFunctional R) ⟶
      primeCutoffPersistence R (primeValueFunctional R) where
  app N := twoPrimeCoreChainProjection R c N
  naturality {N M} h := by
    apply HomologicalComplex.Hom.ext
    funext k
    rfl

/-- Each original chain projection is idempotent. -/
theorem twoPrimeCoreChainProjection_idempotent (c : TwoPrimeCoreFace) (N : ℕ) :
    twoPrimeCoreChainProjection R c N ≫ twoPrimeCoreChainProjection R c N =
      twoPrimeCoreChainProjection R c N := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (twoPrimeCoreProjection_idempotent R k c) x.val

/-- Different cores yield orthogonal endomorphisms of the original chain complex. -/
theorem twoPrimeCoreChainProjection_orthogonal (c d : TwoPrimeCoreFace) (h : c ≠ d) (N : ℕ) :
    twoPrimeCoreChainProjection R c N ≫ twoPrimeCoreChainProjection R d N = 0 := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (twoPrimeCoreProjection_orthogonal R k d c (Ne.symm h)) x.val

#print axioms twoPrimeCoreChainProjectionNat
#print axioms twoPrimeCoreChainProjection_idempotent
#print axioms twoPrimeCoreChainProjection_orthogonal
#print axioms twoPrimeCoreProjection_sum
#print axioms twoPrimeCoreProjection_boundary
#print axioms twoPrimeCoreProjection_cutoff
#print axioms twoPrimeCoreProjection_idempotent
#print axioms twoPrimeCoreProjection_orthogonal
end GaloisForLFunctions.EffectiveScalingGeometry
