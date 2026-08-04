import GaloisForLFunctions.HTGeometry.NonautonomousIsogenyTransport
import GaloisForLFunctions.HTGeometry.NonautonomousJetVelocityTransport

/-!
# The persistent data of a protocol is a flat system over discrete time

Putting the two halves together: the erased sector of a protocol supplies the position subgroups, and
its steps supply the transport.  For a protocol whose steps are open, continuous and bijective on base
points and bijective on jets, the persistent position–velocity data at any two phases are canonically
isomorphic, with no hypothesis left to supply.

In the purely expanding case the erased sector is everything, the position sector collapses, and the
persistent data is the Maurer–Cartan velocity alone.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

/-! ### The expanding case -/

variable {J : Type u} {P : Type v} [CommGroup J] [CommGroup P]

theorem subsingleton_quotient_top : Subsingleton (P ⧸ (⊤ : Subgroup P)) :=
  ⟨fun a b => by
    refine QuotientGroup.induction_on a ?_
    intro x
    refine QuotientGroup.induction_on b ?_
    intro y
    exact QuotientGroup.eq.2 (Subgroup.mem_top _)⟩

instance uniqueQuotientTop : Unique (P ⧸ (⊤ : Subgroup P)) :=
  letI := subsingleton_quotient_top (P := P)
  uniqueOfSubsingleton (1 : P ⧸ (⊤ : Subgroup P))

/-- **The purely expanding case.**  When the protocol erases every direction, the position sector
collapses and the persistent data is the Maurer–Cartan velocity alone. -/
def expandingPositionVelocityEquiv (S : SplitJetEvaluation J P) :
    (P ⧸ (⊤ : Subgroup P)) × S.eval.ker ≃* S.eval.ker :=
  MulEquiv.uniqueProd

/-! ### The flat system -/

variable {Jp : ℕ → Type u} {Pp : ℕ → Type v} [∀ i, CommGroup (Jp i)] [∀ i, CommGroup (Pp i)]
variable [∀ i, TopologicalSpace (Pp i)] [∀ i, IsTopologicalGroup (Pp i)]

/-- **The persistent position–velocity system of a protocol is flat, with nothing left to assume.**
The position subgroups are the erased sectors of the protocol itself, and their transport is a
theorem rather than a hypothesis. -/
def protocolErasedPositionVelocityTransport
    (S : ∀ i, SplitJetEvaluation (Jp i) (Pp i))
    (f : ∀ i, SplitJetMorphism (S i) (S (i + 1)))
    (hopen : ∀ i, IsOpenMap (f i).base) (hcont : ∀ i, Continuous (f i).base)
    (hjets : ∀ i, Function.Bijective (f i).jets)
    (hbase : ∀ i, Function.Bijective (f i).base) (i n : ℕ) :
    (Pp i ⧸ erasedClosure (fun j => (f j).base) i) × (S i).eval.ker
      ≃* (Pp (i + n) ⧸ erasedClosure (fun j => (f j).base) (i + n)) × (S (i + n)).eval.ker :=
  protocolPositionVelocityTransport S f (fun j => erasedClosure (fun k => (f k).base) j)
    (fun j => erasedClosure_comap (fun k => (f k).base) hopen hcont j) hjets hbase i n

/-- **The phase invariants are position and velocity.**  At every phase, the jets modulo the
translations by the erased sector are exactly the reversible position together with the Maurer–Cartan
velocity. -/
def erasedQuotientEquivPositionVelocity
    (S : ∀ i, SplitJetEvaluation (Jp i) (Pp i))
    (f : ∀ i, SplitJetMorphism (S i) (S (i + 1))) (i : ℕ) :
    Jp i ⧸ (erasedClosure (fun j => (f j).base) i).map (S i).const
      ≃* (Pp i ⧸ erasedClosure (fun j => (f j).base) i) × (S i).eval.ker :=
  (S i).quotientSubgroupEquivPositionVelocity _

/-- **The purely expanding phase invariants.**  If the protocol erases every base direction at a
phase, the invariants there are the Maurer–Cartan velocity alone. -/
def expandingErasedQuotientEquivVelocity
    (S : ∀ i, SplitJetEvaluation (Jp i) (Pp i))
    (f : ∀ i, SplitJetMorphism (S i) (S (i + 1))) (i : ℕ)
    (hfull : erasedClosure (fun j => (f j).base) i = ⊤) :
    Jp i ⧸ (erasedClosure (fun j => (f j).base) i).map (S i).const ≃* (S i).eval.ker :=
  (erasedQuotientEquivPositionVelocity S f i).trans
    ((MulEquiv.prodCongr (QuotientGroup.quotientMulEquivOfEq hfull) (MulEquiv.refl _)).trans
      (expandingPositionVelocityEquiv (S i)))

/-- **Holonomy of the persistent data of a periodic protocol.** -/
def protocolPositionVelocityHolonomy
    (S : ∀ i, SplitJetEvaluation (Jp i) (Pp i))
    (f : ∀ i, SplitJetMorphism (S i) (S (i + 1)))
    (hopen : ∀ i, IsOpenMap (f i).base) (hcont : ∀ i, Continuous (f i).base)
    (hjets : ∀ i, Function.Bijective (f i).jets)
    (hbase : ∀ i, Function.Bijective (f i).base) (i p : ℕ)
    (period : (Pp (i + p) ⧸ erasedClosure (fun j => (f j).base) (i + p)) × (S (i + p)).eval.ker
      ≃* (Pp i ⧸ erasedClosure (fun j => (f j).base) i) × (S i).eval.ker) :
    (Pp i ⧸ erasedClosure (fun j => (f j).base) i) × (S i).eval.ker
      ≃* (Pp i ⧸ erasedClosure (fun j => (f j).base) i) × (S i).eval.ker :=
  (protocolErasedPositionVelocityTransport S f hopen hcont hjets hbase i p).trans period

end

end GaloisForLFunctions.HTGeometry
