import GaloisForLFunctions.HTGeometry.CDGAModule

/-!
# Cell attachments under quasi-isomorphisms of both base and cell

A cell attachment is a differential graded module whose carrier is a product `M n × N n` and whose
differential is triangular: the base differential, the cell differential, and a twisting cochain
from the cell to the base.  A comparison of two attachments therefore has two halves, one on each
factor.

When only the base changes, a chase on cocycles suffices and no cohomology of the cell in degree
zero is involved.  When the cell changes as well, the chase needs the cell comparison to be
bijective on cocycles in degree zero — which for a nonnegatively graded complex *is* its cohomology
there, but is not part of `IsQuasiIso`, whose degree `n` component is `H^{n+1}`.  `IsQuasiIsoFull`
adds exactly that missing degree.

* `HTGeometry.CDGAModuleHom.IsQuasiIsoFull` : bijective on cohomology in every degree.
* `HTGeometry.CDGAModuleHom.twistedMap₂` : the comparison of two cell attachments.
* `HTGeometry.CDGAModuleHom.IsQuasiIsoFull.twistedMap₂` : it is a full quasi-isomorphism as soon as
  both halves are.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

namespace CDGAModuleHom

section CellInvariance

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {N' : ℕ → Type w} [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}
  {Q : CDGAModuleStructure A N} {Q' : CDGAModuleStructure A N'}

/-- **A full quasi-isomorphism**: bijective on cohomology in every degree.  For a nonnegatively
graded complex the cohomology in degree zero is the module of cocycles itself, which is the extra
condition over `IsQuasiIso`. -/
def IsQuasiIsoFull (φ : CDGAModuleHom P P') : Prop :=
  Function.Bijective (φ.cocyclesMap 0) ∧ φ.IsQuasiIso

theorem IsQuasiIsoFull.isQuasiIso {φ : CDGAModuleHom P P'} (hφ : φ.IsQuasiIsoFull) :
    φ.IsQuasiIso := hφ.2

/-- **A degreewise bijective morphism is a full quasi-isomorphism.** -/
theorem IsQuasiIsoFull.of_bijective {φ : CDGAModuleHom P P'}
    (hφ : ∀ n, Function.Bijective (φ.toFun n)) : φ.IsQuasiIsoFull := by
  refine ⟨⟨?_, ?_⟩, IsQuasiIso.of_bijective hφ⟩
  · intro a b hab
    exact Subtype.ext ((hφ 0).1 (congrArg Subtype.val hab))
  · intro y'
    obtain ⟨m, hm⟩ := (hφ 0).2 (y' : M' 0)
    have hcoc : m ∈ P.cocycles 0 := by
      have h1 : φ.toFun 1 (P.d 0 m) = φ.toFun 1 (0 : M 1) := by
        rw [φ.map_d 0 m, hm, show φ.toFun 1 (0 : M 1) = 0 from (φ.mapₗ 1).map_zero]
        exact y'.2
      exact (hφ 1).1 h1
    exact ⟨⟨m, hcoc⟩, Subtype.ext hm⟩

section TwoOutOfThree

variable {L : ℕ → Type w} [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
  {S : CDGAModuleStructure A L}

theorem cocyclesMap_comp' (χ : CDGAModuleHom P' S) (φ : CDGAModuleHom P P') (n : ℕ) :
    (χ.comp φ).cocyclesMap n = (χ.cocyclesMap n).comp (φ.cocyclesMap n) := rfl

theorem IsQuasiIsoFull.comp {χ : CDGAModuleHom P' S} {φ : CDGAModuleHom P P'}
    (hχ : χ.IsQuasiIsoFull) (hφ : φ.IsQuasiIsoFull) : (χ.comp φ).IsQuasiIsoFull := by
  refine ⟨?_, IsQuasiIso.comp hχ.2 hφ.2⟩
  rw [cocyclesMap_comp', LinearMap.coe_comp]
  exact hχ.1.comp hφ.1

/-- **Two out of three, left** for full quasi-isomorphisms. -/
theorem IsQuasiIsoFull.of_comp_left {χ : CDGAModuleHom P' S} {φ : CDGAModuleHom P P'}
    (hcomp : (χ.comp φ).IsQuasiIsoFull) (hφ : φ.IsQuasiIsoFull) : χ.IsQuasiIsoFull := by
  refine ⟨?_, IsQuasiIso.of_comp_left hcomp.2 hφ.2⟩
  have h := hcomp.1
  rw [cocyclesMap_comp', LinearMap.coe_comp] at h
  exact (Function.Bijective.of_comp_iff _ hφ.1).1 h

/-- **Two out of three, right** for full quasi-isomorphisms. -/
theorem IsQuasiIsoFull.of_comp_right {χ : CDGAModuleHom P' S} {φ : CDGAModuleHom P P'}
    (hcomp : (χ.comp φ).IsQuasiIsoFull) (hχ : χ.IsQuasiIsoFull) : φ.IsQuasiIsoFull := by
  refine ⟨?_, IsQuasiIso.of_comp_right hcomp.2 hχ.2⟩
  have h := hcomp.1
  rw [cocyclesMap_comp', LinearMap.coe_comp] at h
  exact (Function.Bijective.of_comp_iff' hχ.1 _).1 h

end TwoOutOfThree

/-- **The comparison of two cell attachments** induced by a map of bases and a map of cells that
intertwine the twisting cochains. -/
def twistedMap₂ (t : CDGATwist P Q) (t' : CDGATwist P' Q') (φ : CDGAModuleHom P P')
    (ψ : CDGAModuleHom Q Q')
    (hcompat : ∀ (n : ℕ) (c : N n), φ.toFun (n + 1) (t.τ n c) = t'.τ n (ψ.toFun n c)) :
    CDGAModuleHom (CDGAModuleStructure.twisted P Q t) (CDGAModuleStructure.twisted P' Q' t') where
  toFun n m := (φ.toFun n m.1, ψ.toFun n m.2)
  map_add n m m' := Prod.ext (φ.map_add n m.1 m'.1) (ψ.map_add n m.2 m'.2)
  map_smul n c m := Prod.ext (φ.map_smul n c m.1) (ψ.map_smul n c m.2)
  map_act h x m := Prod.ext (φ.map_act h x m.1) (ψ.map_act h x m.2)
  map_d n m := by
    refine Prod.ext ?_ (ψ.map_d n m.2)
    show φ.toFun (n + 1) (P.d n m.1 + t.τ n m.2)
      = P'.d n (φ.toFun n m.1) + t'.τ n (ψ.toFun n m.2)
    rw [φ.map_add, φ.map_d, hcompat]

@[simp] theorem twistedMap₂_toFun (t : CDGATwist P Q) (t' : CDGATwist P' Q')
    (φ : CDGAModuleHom P P') (ψ : CDGAModuleHom Q Q')
    (hcompat : ∀ (n : ℕ) (c : N n), φ.toFun (n + 1) (t.τ n c) = t'.τ n (ψ.toFun n c)) (n : ℕ)
    (m : M n × N n) :
    (twistedMap₂ t t' φ ψ hcompat).toFun n m = (φ.toFun n m.1, ψ.toFun n m.2) := rfl

section Chase

variable {t : CDGATwist P Q} {t' : CDGATwist P' Q'} {φ : CDGAModuleHom P P'}
  {ψ : CDGAModuleHom Q Q'}
  (hcompat : ∀ (n : ℕ) (c : N n), φ.toFun (n + 1) (t.τ n c) = t'.τ n (ψ.toFun n c))

/-- A twist of the cell is `d`-exact whenever the cell it twists is a cocycle: this is the statement
that the twisting cochain descends to a map of cohomology. -/
theorem twist_mem_cocycles (n : ℕ) (c : N n) (hc : Q.d n c = 0) :
    t.τ n c ∈ P.cocycles (n + 1) := by
  show P.d (n + 1) (t.τ n c) = 0
  rw [eq_neg_iff_add_eq_zero.2 (t.τ_d n c), hc, CDGAModuleStructure.CDGATwist.τ_zero, neg_zero]

include hcompat in
/-- **A cocycle of the cell downstairs is, modulo a coboundary of the base, the twist of a cocycle
of the cell upstairs.**  In positive degree this is surjectivity of the cell comparison on
cohomology; in degree zero it is surjectivity on cocycles, which is why the full notion is needed.
-/
theorem exists_twist_eq_of_cocycle (hψ : ψ.IsQuasiIsoFull) (n : ℕ) (z : N' n)
    (hz : Q'.d n z = 0) :
    ∃ (z₀ : N n) (v : M' n), Q.d n z₀ = 0 ∧
      t'.τ n z = φ.toFun (n + 1) (t.τ n z₀) + P'.d n v := by
  cases n with
  | zero =>
      obtain ⟨z₀, hz₀⟩ := hψ.1.2 ⟨z, hz⟩
      refine ⟨(z₀ : N 0), 0, z₀.2, ?_⟩
      rw [hcompat 0 (z₀ : N 0), show ψ.toFun 0 (z₀ : N 0) = z from congrArg Subtype.val hz₀,
        show P'.d 0 (0 : M' 0) = 0 from (P'.dₗ 0).map_zero, add_zero]
  | succ k =>
      obtain ⟨z₀, w, hw⟩ := exists_cocycle_sub_eq_d hψ.2 k ⟨z, hz⟩
      refine ⟨(z₀ : N (k + 1)), t'.τ k w, z₀.2, ?_⟩
      have hz' : z = ψ.toFun (k + 1) (z₀ : N (k + 1)) - Q'.d k w := by
        rw [← hw]; abel
      rw [hz', show t'.τ (k + 1) (ψ.toFun (k + 1) (z₀ : N (k + 1)) - Q'.d k w)
          = t'.τ (k + 1) (ψ.toFun (k + 1) (z₀ : N (k + 1))) - t'.τ (k + 1) (Q'.d k w)
        from map_sub (t'.τₗ (k + 1)) _ _, ← hcompat (k + 1) (z₀ : N (k + 1)),
        eq_neg_iff_add_eq_zero.2 ((add_comm _ _).trans (t'.τ_d k w))]
      abel

include hcompat in
/-- **A cocycle of a cell attachment whose image is a coboundary is a coboundary.** -/
theorem twisted_mem_coboundaries₂ (hφ : φ.IsQuasiIsoFull) (hψ : ψ.IsQuasiIsoFull) (n : ℕ)
    (u : (CDGAModuleStructure.twisted P Q t).cocycles (n + 1))
    (hu : (twistedMap₂ t t' φ ψ hcompat).cocyclesMap (n + 1) u
      ∈ (CDGAModuleStructure.twisted P' Q' t').coboundaries n) :
    u ∈ (CDGAModuleStructure.twisted P Q t).coboundaries n := by
  obtain ⟨⟨u₁, u₂⟩, hu0⟩ := u
  obtain ⟨pq, hpq⟩ := (CDGAModuleStructure.mem_coboundaries _).1 hu
  have hp : φ.toFun (n + 1) u₁ = P'.d n pq.1 + t'.τ n pq.2 := congrArg Prod.fst hpq
  have hq : ψ.toFun (n + 1) u₂ = Q'.d n pq.2 := congrArg Prod.snd hpq
  have hc1 : P.d (n + 1) u₁ + t.τ (n + 1) u₂ = 0 := congrArg Prod.fst hu0
  have hc2 : Q.d (n + 1) u₂ = 0 := congrArg Prod.snd hu0
  obtain ⟨q₀, hq₀0⟩ := exists_eq_d_of_map_eq_d hψ.2 n ⟨u₂, hc2⟩ pq.2 hq
  have hq₀ : u₂ = Q.d n q₀ := hq₀0
  have hycoc : (u₁ - t.τ n q₀) ∈ P.cocycles (n + 1) := by
    show P.d (n + 1) (u₁ - t.τ n q₀) = 0
    rw [show P.d (n + 1) (u₁ - t.τ n q₀) = P.d (n + 1) u₁ - P.d (n + 1) (t.τ n q₀)
        from map_sub (P.dₗ (n + 1)) _ _, eq_neg_iff_add_eq_zero.2 hc1,
      eq_neg_iff_add_eq_zero.2 (t.τ_d n q₀), ← hq₀]
    abel
  have hzcoc : Q'.d n (ψ.toFun n q₀ - pq.2) = 0 := by
    rw [show Q'.d n (ψ.toFun n q₀ - pq.2) = Q'.d n (ψ.toFun n q₀) - Q'.d n pq.2
        from map_sub (Q'.dₗ n) _ _, ← ψ.map_d n q₀, ← hq₀, hq]
    abel
  obtain ⟨z₀, v, hz₀, hzv⟩ :=
    exists_twist_eq_of_cocycle hcompat hψ n (ψ.toFun n q₀ - pq.2) hzcoc
  have htz : t.τ n z₀ ∈ P.cocycles (n + 1) := twist_mem_cocycles n z₀ hz₀
  have hyzcoc : (u₁ - t.τ n q₀ + t.τ n z₀) ∈ P.cocycles (n + 1) := by
    show P.d (n + 1) (u₁ - t.τ n q₀ + t.τ n z₀) = 0
    rw [show P.d (n + 1) (u₁ - t.τ n q₀ + t.τ n z₀)
        = P.d (n + 1) (u₁ - t.τ n q₀) + P.d (n + 1) (t.τ n z₀) from P.d_add _ _ _,
      show P.d (n + 1) (u₁ - t.τ n q₀) = 0 from hycoc, show P.d (n + 1) (t.τ n z₀) = 0 from htz]
    abel
  have hφy : φ.toFun (n + 1) (u₁ - t.τ n q₀ + t.τ n z₀) = P'.d n (pq.1 - v) := by
    rw [show φ.toFun (n + 1) (u₁ - t.τ n q₀ + t.τ n z₀)
        = φ.toFun (n + 1) (u₁ - t.τ n q₀) + φ.toFun (n + 1) (t.τ n z₀)
      from φ.map_add _ _ _,
      show φ.toFun (n + 1) (u₁ - t.τ n q₀)
        = φ.toFun (n + 1) u₁ - φ.toFun (n + 1) (t.τ n q₀) from map_sub (φ.mapₗ (n + 1)) _ _,
      hp, hcompat n q₀,
      show P'.d n (pq.1 - v) = P'.d n pq.1 - P'.d n v from map_sub (P'.dₗ n) _ _,
      show φ.toFun (n + 1) (t.τ n z₀) = t'.τ n (ψ.toFun n q₀ - pq.2) - P'.d n v by
        rw [hzv]; abel,
      show t'.τ n (ψ.toFun n q₀ - pq.2) = t'.τ n (ψ.toFun n q₀) - t'.τ n pq.2
        from map_sub (t'.τₗ n) _ _]
    abel
  obtain ⟨m₀, hm₀0⟩ := exists_eq_d_of_map_eq_d hφ.2 n ⟨_, hyzcoc⟩ (pq.1 - v) hφy
  have hm₀ : u₁ - t.τ n q₀ + t.τ n z₀ = P.d n m₀ := hm₀0
  refine (CDGAModuleStructure.mem_coboundaries _).2 ⟨(m₀, q₀ - z₀), ?_⟩
  refine Prod.ext ?_ ?_
  · show u₁ = P.d n m₀ + t.τ n (q₀ - z₀)
    rw [← hm₀, show t.τ n (q₀ - z₀) = t.τ n q₀ - t.τ n z₀ from map_sub (t.τₗ n) _ _]
    abel
  · show u₂ = Q.d n (q₀ - z₀)
    rw [show Q.d n (q₀ - z₀) = Q.d n q₀ - Q.d n z₀ from map_sub (Q.dₗ n) _ _, hz₀, ← hq₀]
    abel

include hcompat in
/-- **Every cohomology class of a cell attachment downstairs is hit.** -/
theorem twisted_cohomology_surjective₂ (hφ : φ.IsQuasiIsoFull) (hψ : ψ.IsQuasiIsoFull) (n : ℕ) :
    Function.Surjective ((twistedMap₂ t t' φ ψ hcompat).cohomologyMap n) := by
  refine fun cl => Quotient.inductionOn' cl fun u' => ?_
  obtain ⟨⟨u₁, u₂⟩, hu0⟩ := u'
  have hc1 : P'.d (n + 1) u₁ + t'.τ (n + 1) u₂ = 0 := congrArg Prod.fst hu0
  have hc2 : Q'.d (n + 1) u₂ = 0 := congrArg Prod.snd hu0
  obtain ⟨c, w, hcw⟩ := exists_cocycle_sub_eq_d hψ.2 n ⟨u₂, hc2⟩
  have htcoc : t.τ (n + 1) (c : N (n + 1)) ∈ P.cocycles (n + 1 + 1) :=
    twist_mem_cocycles (n + 1) (c : N (n + 1)) c.2
  have hψc : ψ.toFun (n + 1) (c : N (n + 1)) = u₂ + Q'.d n w := by
    rw [← hcw]; abel
  have hφt : φ.toFun (n + 1 + 1) (t.τ (n + 1) (c : N (n + 1)))
      = P'.d (n + 1) (-(u₁ + t'.τ n w)) := by
    rw [hcompat (n + 1) (c : N (n + 1)), hψc,
      show t'.τ (n + 1) (u₂ + Q'.d n w) = t'.τ (n + 1) u₂ + t'.τ (n + 1) (Q'.d n w)
        from t'.τ_add _ _ _,
      eq_neg_iff_add_eq_zero.2 ((add_comm _ _).trans hc1),
      eq_neg_iff_add_eq_zero.2 ((add_comm _ _).trans (t'.τ_d n w)),
      show P'.d (n + 1) (-(u₁ + t'.τ n w)) = -P'.d (n + 1) (u₁ + t'.τ n w)
        from map_neg (P'.dₗ (n + 1)) _,
      show P'.d (n + 1) (u₁ + t'.τ n w) = P'.d (n + 1) u₁ + P'.d (n + 1) (t'.τ n w)
        from P'.d_add _ _ _]
    abel
  obtain ⟨m₀, hm₀0⟩ :=
    exists_eq_d_of_map_eq_d hφ.2 (n + 1) ⟨_, htcoc⟩ (-(u₁ + t'.τ n w)) hφt
  have hm₀ : t.τ (n + 1) (c : N (n + 1)) = P.d (n + 1) m₀ := hm₀0
  have hdm : P.d (n + 1) (-m₀) = -t.τ (n + 1) (c : N (n + 1)) := by
    rw [show P.d (n + 1) (-m₀) = -P.d (n + 1) m₀ from map_neg (P.dₗ (n + 1)) _, ← hm₀]
  have hecoc : (φ.toFun (n + 1) (-m₀) - u₁ - t'.τ n w) ∈ P'.cocycles (n + 1) := by
    show P'.d (n + 1) (φ.toFun (n + 1) (-m₀) - u₁ - t'.τ n w) = 0
    rw [show P'.d (n + 1) (φ.toFun (n + 1) (-m₀) - u₁ - t'.τ n w)
        = P'.d (n + 1) (φ.toFun (n + 1) (-m₀) - u₁) - P'.d (n + 1) (t'.τ n w)
      from map_sub (P'.dₗ (n + 1)) _ _,
      show P'.d (n + 1) (φ.toFun (n + 1) (-m₀) - u₁)
        = P'.d (n + 1) (φ.toFun (n + 1) (-m₀)) - P'.d (n + 1) u₁
      from map_sub (P'.dₗ (n + 1)) _ _, ← φ.map_d (n + 1) (-m₀), hdm,
      show φ.toFun (n + 1 + 1) (-t.τ (n + 1) (c : N (n + 1)))
        = -φ.toFun (n + 1 + 1) (t.τ (n + 1) (c : N (n + 1)))
      from map_neg (φ.mapₗ (n + 1 + 1)) _, hcompat (n + 1) (c : N (n + 1)), hψc,
      show t'.τ (n + 1) (u₂ + Q'.d n w) = t'.τ (n + 1) u₂ + t'.τ (n + 1) (Q'.d n w)
        from t'.τ_add _ _ _,
      eq_neg_iff_add_eq_zero.2 ((add_comm _ _).trans hc1),
      eq_neg_iff_add_eq_zero.2 ((add_comm _ _).trans (t'.τ_d n w))]
    abel
  obtain ⟨y, v, hyv⟩ := exists_cocycle_sub_eq_d hφ.2 n ⟨_, hecoc⟩
  have hnew : ((-m₀ - (y : M (n + 1)), (c : N (n + 1))) : M (n + 1) × N (n + 1))
      ∈ (CDGAModuleStructure.twisted P Q t).cocycles (n + 1) := by
    refine Prod.ext ?_ c.2
    show P.d (n + 1) (-m₀ - (y : M (n + 1))) + t.τ (n + 1) (c : N (n + 1)) = 0
    rw [show P.d (n + 1) (-m₀ - (y : M (n + 1)))
        = P.d (n + 1) (-m₀) - P.d (n + 1) (y : M (n + 1)) from map_sub (P.dₗ (n + 1)) _ _,
      show P.d (n + 1) (y : M (n + 1)) = 0 from y.2, hdm]
    abel
  refine ⟨Submodule.Quotient.mk ⟨_, hnew⟩, ?_⟩
  show Submodule.Quotient.mk
    ((twistedMap₂ t t' φ ψ hcompat).cocyclesMap (n + 1) ⟨_, hnew⟩) = _
  refine (Submodule.Quotient.eq _).2 ((CDGAModuleStructure.mem_coboundaries _).2 ⟨(-v, w), ?_⟩)
  refine Prod.ext ?_ ?_
  · show φ.toFun (n + 1) (-m₀ - (y : M (n + 1))) - u₁ = P'.d n (-v) + t'.τ n w
    rw [show φ.toFun (n + 1) (-m₀ - (y : M (n + 1)))
        = φ.toFun (n + 1) (-m₀) - φ.toFun (n + 1) (y : M (n + 1))
      from map_sub (φ.mapₗ (n + 1)) _ _,
      show P'.d n (-v) = -P'.d n v from map_neg (P'.dₗ n) _]
    have hyv' : φ.toFun (n + 1) (y : M (n + 1))
        - (φ.toFun (n + 1) (-m₀) - u₁ - t'.τ n w) = P'.d n v := hyv
    rw [← hyv']
    abel
  · show ψ.toFun (n + 1) (c : N (n + 1)) - u₂ = Q'.d n w
    rw [hψc]
    abel

include hcompat in
/-- **The comparison of two cell attachments is bijective on cocycles in degree zero** whenever both
halves are. -/
theorem twistedMap₂_cocyclesMap_zero_bijective (hφ : φ.IsQuasiIsoFull) (hψ : ψ.IsQuasiIsoFull) :
    Function.Bijective ((twistedMap₂ t t' φ ψ hcompat).cocyclesMap 0) := by
  constructor
  · rintro ⟨⟨a₁, a₂⟩, ha⟩ ⟨⟨b₁, b₂⟩, hb⟩ hab
    have ha1 : P.d 0 a₁ + t.τ 0 a₂ = 0 := congrArg Prod.fst ha
    have ha2 : Q.d 0 a₂ = 0 := congrArg Prod.snd ha
    have hb1 : P.d 0 b₁ + t.τ 0 b₂ = 0 := congrArg Prod.fst hb
    have hb2 : Q.d 0 b₂ = 0 := congrArg Prod.snd hb
    have hval := congrArg Subtype.val hab
    have hf : φ.toFun 0 a₁ = φ.toFun 0 b₁ := congrArg Prod.fst hval
    have hg : ψ.toFun 0 a₂ = ψ.toFun 0 b₂ := congrArg Prod.snd hval
    have h2 : a₂ = b₂ := congrArg Subtype.val
      (hψ.1.1 (show ψ.cocyclesMap 0 ⟨a₂, ha2⟩ = ψ.cocyclesMap 0 ⟨b₂, hb2⟩ from Subtype.ext hg))
    have hd : P.d 0 (a₁ - b₁) = 0 := by
      rw [show P.d 0 (a₁ - b₁) = P.d 0 a₁ - P.d 0 b₁ from map_sub (P.dₗ 0) _ _,
        eq_neg_iff_add_eq_zero.2 ha1, eq_neg_iff_add_eq_zero.2 hb1, h2]
      abel
    have hz : P.d 0 (0 : M 0) = 0 := (P.dₗ 0).map_zero
    have h1 : a₁ - b₁ = 0 := congrArg Subtype.val
      (hφ.1.1 (show φ.cocyclesMap 0 ⟨a₁ - b₁, hd⟩ = φ.cocyclesMap 0 ⟨(0 : M 0), hz⟩ from
        Subtype.ext (by
          show φ.toFun 0 (a₁ - b₁) = φ.toFun 0 (0 : M 0)
          rw [show φ.toFun 0 (a₁ - b₁) = φ.toFun 0 a₁ - φ.toFun 0 b₁ from map_sub (φ.mapₗ 0) _ _,
            hf, sub_self, show φ.toFun 0 (0 : M 0) = 0 from (φ.mapₗ 0).map_zero])))
    exact Subtype.ext (Prod.ext (sub_eq_zero.1 h1) h2)
  · rintro ⟨⟨u₁, u₂⟩, hu⟩
    have hc1 : P'.d 0 u₁ + t'.τ 0 u₂ = 0 := congrArg Prod.fst hu
    have hc2 : Q'.d 0 u₂ = 0 := congrArg Prod.snd hu
    obtain ⟨c, hc⟩ := hψ.1.2 ⟨u₂, hc2⟩
    have hψc : ψ.toFun 0 (c : N 0) = u₂ := congrArg Subtype.val hc
    have htcoc : t.τ 0 (c : N 0) ∈ P.cocycles 1 := twist_mem_cocycles 0 (c : N 0) c.2
    have hφt : φ.toFun 1 (t.τ 0 (c : N 0)) = P'.d 0 (-u₁) := by
      rw [hcompat 0 (c : N 0), hψc,
        show P'.d 0 (-u₁) = -P'.d 0 u₁ from map_neg (P'.dₗ 0) _,
        eq_neg_iff_add_eq_zero.2 ((add_comm _ _).trans hc1)]
    obtain ⟨m₀, hm₀0⟩ := exists_eq_d_of_map_eq_d hφ.2 0 ⟨_, htcoc⟩ (-u₁) hφt
    have hm₀ : t.τ 0 (c : N 0) = P.d 0 m₀ := hm₀0
    have hdm : P.d 0 (-m₀) = -t.τ 0 (c : N 0) := by
      rw [show P.d 0 (-m₀) = -P.d 0 m₀ from map_neg (P.dₗ 0) _, ← hm₀]
    have hecoc : (φ.toFun 0 (-m₀) - u₁) ∈ P'.cocycles 0 := by
      show P'.d 0 (φ.toFun 0 (-m₀) - u₁) = 0
      rw [show P'.d 0 (φ.toFun 0 (-m₀) - u₁) = P'.d 0 (φ.toFun 0 (-m₀)) - P'.d 0 u₁
          from map_sub (P'.dₗ 0) _ _, ← φ.map_d 0 (-m₀), hdm,
        show φ.toFun 1 (-t.τ 0 (c : N 0)) = -φ.toFun 1 (t.τ 0 (c : N 0))
          from map_neg (φ.mapₗ 1) _, hcompat 0 (c : N 0), hψc,
        eq_neg_iff_add_eq_zero.2 ((add_comm _ _).trans hc1)]
      abel
    obtain ⟨y, hy⟩ := hφ.1.2 ⟨_, hecoc⟩
    have hyv : φ.toFun 0 (y : M 0) = φ.toFun 0 (-m₀) - u₁ := congrArg Subtype.val hy
    have hnew : ((-m₀ - (y : M 0), (c : N 0)) : M 0 × N 0)
        ∈ (CDGAModuleStructure.twisted P Q t).cocycles 0 := by
      refine Prod.ext ?_ c.2
      show P.d 0 (-m₀ - (y : M 0)) + t.τ 0 (c : N 0) = 0
      rw [show P.d 0 (-m₀ - (y : M 0)) = P.d 0 (-m₀) - P.d 0 (y : M 0)
          from map_sub (P.dₗ 0) _ _, show P.d 0 (y : M 0) = 0 from y.2, hdm]
      abel
    refine ⟨⟨_, hnew⟩, Subtype.ext (Prod.ext ?_ hψc)⟩
    show φ.toFun 0 (-m₀ - (y : M 0)) = u₁
    rw [show φ.toFun 0 (-m₀ - (y : M 0)) = φ.toFun 0 (-m₀) - φ.toFun 0 (y : M 0)
        from map_sub (φ.mapₗ 0) _ _, hyv]
    abel

include hcompat in
/-- **Attaching a cell preserves full quasi-isomorphisms.**  A comparison of cell attachments whose
base half and cell half are both full quasi-isomorphisms is one.  Together with `tower_isQuasiIso`
this is the invariance statement for a semi-free resolution: it is what lets a quasi-isomorphism be
propagated through a tower whose cells also change. -/
theorem IsQuasiIsoFull.twistedMap₂ (hφ : φ.IsQuasiIsoFull) (hψ : ψ.IsQuasiIsoFull) :
    (CDGAModuleHom.twistedMap₂ t t' φ ψ hcompat).IsQuasiIsoFull := by
  refine ⟨twistedMap₂_cocyclesMap_zero_bijective hcompat hφ hψ, fun n => ⟨?_, ?_⟩⟩
  · refine fun a b => Quotient.inductionOn₂' a b fun u v hab => ?_
    have h2 := (Submodule.Quotient.eq _).1 hab
    have h3 : (CDGAModuleHom.twistedMap₂ t t' φ ψ hcompat).cocyclesMap (n + 1) (u - v)
        ∈ (CDGAModuleStructure.twisted P' Q' t').coboundaries n := by
      rw [map_sub]
      exact h2
    exact (Submodule.Quotient.eq _).2
      (twisted_mem_coboundaries₂ hcompat hφ hψ n (u - v) h3)
  · exact twisted_cohomology_surjective₂ hcompat hφ hψ n

end Chase

end CellInvariance

section PiFull

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} {ι : Type*}
  {M : ι → ℕ → Type w} [∀ i n, AddCommGroup (M i n)] [∀ i n, Module R (M i n)]
  {N : ι → ℕ → Type w} [∀ i n, AddCommGroup (N i n)] [∀ i n, Module R (N i n)]
  {P : ∀ i, CDGAModuleStructure A (M i)} {Q : ∀ i, CDGAModuleStructure A (N i)}

/-- **A product of full quasi-isomorphisms is a full quasi-isomorphism.**  A family is a cocycle
exactly when each of its components is, so the degree-zero half is read off componentwise. -/
theorem IsQuasiIsoFull.piMap {φ : ∀ i, CDGAModuleHom (P i) (Q i)}
    (hφ : ∀ i, (φ i).IsQuasiIsoFull) : (CDGAModuleHom.piMap φ).IsQuasiIsoFull := by
  classical
  refine ⟨⟨?_, ?_⟩, IsQuasiIso.piMap fun i => (hφ i).2⟩
  · intro a b hab
    refine Subtype.ext (funext fun i => ?_)
    have h1 : (φ i).cocyclesMap 0
          ⟨(a : ∀ j, M j 0) i, CDGAModuleStructure.mem_pi_cocycles.1 a.2 i⟩
        = (φ i).cocyclesMap 0
          ⟨(b : ∀ j, M j 0) i, CDGAModuleStructure.mem_pi_cocycles.1 b.2 i⟩ :=
      Subtype.ext (congrFun (congrArg Subtype.val hab) i)
    exact congrArg Subtype.val ((hφ i).1.1 h1)
  · intro v
    choose u hu using fun i => (hφ i).1.2
      ⟨(v : ∀ j, N j 0) i, CDGAModuleStructure.mem_pi_cocycles.1 v.2 i⟩
    refine ⟨⟨fun i => (u i : M i 0),
      CDGAModuleStructure.mem_pi_cocycles.2 fun i => (u i).2⟩, ?_⟩
    exact Subtype.ext (funext fun i => congrArg Subtype.val (hu i))

end PiFull

end CDGAModuleHom

end GaloisForLFunctions.HTGeometry
