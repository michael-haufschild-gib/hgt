import GaloisForLFunctions.HTGeometry.MaurerCartanJetQuotient

/-!
# Position and velocity transport along a time-dependent protocol

A morphism of split jet evaluations is a map of jets and a map of base points intertwining evaluation
and the constant section.  Maurer–Cartan normalization is natural for such a morphism: the velocity of
a transported jet is the transported velocity.  When the jet map is bijective and the base map is
injective the velocity sector is carried isomorphically, and when the base subgroups correspond the
position sector is too.

So a protocol whose steps are isomorphisms on jets and on base points carries the whole
position–velocity system from phase to phase without loss: the persistent positions and the persistent
Maurer–Cartan velocities form a flat system over discrete time.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v u' v'

variable {J : Type u} {P : Type v} {J' : Type u'} {P' : Type v'}
variable [CommGroup J] [CommGroup P] [CommGroup J'] [CommGroup P']

/-- A step of a time-dependent protocol on split jet evaluations: a map of jets and a map of base
points intertwining evaluation and the constant section. -/
structure SplitJetMorphism (S : SplitJetEvaluation J P) (S' : SplitJetEvaluation J' P') where
  /-- The map on jets. -/
  jets : J →* J'
  /-- The map on base points. -/
  base : P →* P'
  /-- Evaluation is natural. -/
  eval_comm : ∀ j, S'.eval (jets j) = base (S.eval j)
  /-- The constant section is natural. -/
  const_comm : ∀ p, jets (S.const p) = S'.const (base p)

namespace SplitJetMorphism

variable {S : SplitJetEvaluation J P} {S' : SplitJetEvaluation J' P'} (f : SplitJetMorphism S S')

/-- The velocity sector is preserved: an identity-based jet transports to an identity-based jet. -/
def velocity : S.eval.ker →* S'.eval.ker where
  toFun z := ⟨f.jets (z : J), by
    rw [MonoidHom.mem_ker, f.eval_comm, (show S.eval (z : J) = 1 from z.2), map_one]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' z w := by
    apply Subtype.ext
    simp

@[simp]
theorem velocity_coe (z : S.eval.ker) : (f.velocity z : J') = f.jets (z : J) := rfl

/-- **Velocity is natural.**  The Maurer–Cartan velocity of a transported jet is the transported
velocity. -/
theorem normalize_comm (j : J) : S'.normalize (f.jets j) = f.velocity (S.normalize j) := by
  apply Subtype.ext
  rw [SplitJetEvaluation.normalize_coe, velocity_coe, SplitJetEvaluation.normalize_coe,
    map_div, f.eval_comm, f.const_comm]

/-- **The velocity sector transports isomorphically.**  A step which is bijective on jets and
injective on base points carries the velocity sector isomorphically. -/
def velocityEquiv (hj : Function.Bijective f.jets) (hb : Function.Injective f.base) :
    S.eval.ker ≃* S'.eval.ker := by
  refine MulEquiv.ofBijective f.velocity ⟨?_, ?_⟩
  · intro z w hzw
    exact Subtype.ext (hj.1 (congrArg Subtype.val hzw))
  · intro z
    obtain ⟨j, hj'⟩ := hj.2 (z : J')
    have hev : S.eval j = 1 := by
      refine hb ?_
      rw [← f.eval_comm, hj', (show S'.eval (z : J') = 1 from z.2), map_one]
    exact ⟨⟨j, hev⟩, Subtype.ext hj'⟩

/-- **The position sector transports.**  Corresponding base subgroups induce a map of positions. -/
def position (H : Subgroup P) [H.Normal] (H' : Subgroup P') [H'.Normal]
    (h : H ≤ H'.comap f.base) : P ⧸ H →* P' ⧸ H' :=
  QuotientGroup.map H H' f.base h

@[simp]
theorem position_mk (H : Subgroup P) [H.Normal] (H' : Subgroup P') [H'.Normal]
    (h : H ≤ H'.comap f.base) (p : P) :
    f.position H H' h (QuotientGroup.mk p) = QuotientGroup.mk (f.base p) := rfl

/-- **The position sector transports isomorphically** when the base map is surjective and the base
subgroups correspond exactly. -/
def positionEquiv (H : Subgroup P) [H.Normal] (H' : Subgroup P') [H'.Normal]
    (hcomap : H'.comap f.base = H) (hsurj : Function.Surjective f.base) :
    P ⧸ H ≃* P' ⧸ H' := by
  refine MulEquiv.ofBijective (f.position H H' (le_of_eq hcomap.symm)) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_one _).2 ?_
    intro y
    refine QuotientGroup.induction_on y ?_
    intro p hp
    rw [position_mk, QuotientGroup.eq_one_iff] at hp
    rw [QuotientGroup.eq_one_iff]
    have hmem : p ∈ H'.comap f.base := hp
    rwa [hcomap] at hmem
  · intro y
    refine QuotientGroup.induction_on y ?_
    intro p'
    obtain ⟨p, rfl⟩ := hsurj p'
    exact ⟨QuotientGroup.mk p, rfl⟩

/-- **Position–velocity coordinates are natural.**  Transporting a jet and then reading its
position and velocity is reading them first and transporting each sector. -/
theorem positionVelocityHom_comm (H : Subgroup P) (H' : Subgroup P')
    (h : H ≤ H'.comap f.base) (j : J) :
    S'.positionVelocityHom H' (f.jets j)
      = (f.position H H' h (S.positionVelocityHom H j).1,
         f.velocity (S.positionVelocityHom H j).2) := by
  apply Prod.ext
  · change QuotientGroup.mk (S'.eval (f.jets j)) = QuotientGroup.mk (f.base (S.eval j))
    rw [f.eval_comm]
  · exact f.normalize_comm j

/-- **Flat position–velocity transport.**  A step which is bijective on jets, bijective on base
points, and matches the position subgroups carries the whole position–velocity system
isomorphically. -/
def positionVelocityEquiv (H : Subgroup P) [H.Normal] (H' : Subgroup P') [H'.Normal]
    (hcomap : H'.comap f.base = H) (hjets : Function.Bijective f.jets)
    (hbase : Function.Bijective f.base) :
    (P ⧸ H) × S.eval.ker ≃* (P' ⧸ H') × S'.eval.ker :=
  MulEquiv.prodCongr (f.positionEquiv H H' hcomap hbase.2) (f.velocityEquiv hjets hbase.1)

end SplitJetMorphism

/-! ### A time-dependent protocol -/

variable {Jp : ℕ → Type u} {Pp : ℕ → Type v} [∀ i, CommGroup (Jp i)] [∀ i, CommGroup (Pp i)]

/-- **The persistent position–velocity system of a protocol is flat.**  If every step of a protocol
is bijective on jets and on base points and matches the position subgroups, then the
position–velocity data at consecutive phases are canonically isomorphic. -/
def protocolPositionVelocityEquiv
    (S : ∀ i, SplitJetEvaluation (Jp i) (Pp i))
    (f : ∀ i, SplitJetMorphism (S i) (S (i + 1)))
    (H : ∀ i, Subgroup (Pp i)) [∀ i, (H i).Normal]
    (hcomap : ∀ i, (H (i + 1)).comap (f i).base = H i)
    (hjets : ∀ i, Function.Bijective (f i).jets)
    (hbase : ∀ i, Function.Bijective (f i).base) (i : ℕ) :
    (Pp i ⧸ H i) × (S i).eval.ker ≃* (Pp (i + 1) ⧸ H (i + 1)) × (S (i + 1)).eval.ker :=
  (f i).positionVelocityEquiv (H i) (H (i + 1)) (hcomap i) (hjets i) (hbase i)

/-- Flat transport across any number of phases. -/
def protocolPositionVelocityTransport
    (S : ∀ i, SplitJetEvaluation (Jp i) (Pp i))
    (f : ∀ i, SplitJetMorphism (S i) (S (i + 1)))
    (H : ∀ i, Subgroup (Pp i)) [∀ i, (H i).Normal]
    (hcomap : ∀ i, (H (i + 1)).comap (f i).base = H i)
    (hjets : ∀ i, Function.Bijective (f i).jets)
    (hbase : ∀ i, Function.Bijective (f i).base) (i : ℕ) :
    ∀ n : ℕ, (Pp i ⧸ H i) × (S i).eval.ker
      ≃* (Pp (i + n) ⧸ H (i + n)) × (S (i + n)).eval.ker
  | 0 => MulEquiv.refl _
  | n + 1 =>
      (protocolPositionVelocityTransport S f H hcomap hjets hbase i n).trans
        (protocolPositionVelocityEquiv S f H hcomap hjets hbase (i + n))

end

end GaloisForLFunctions.HTGeometry
