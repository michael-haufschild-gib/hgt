import GaloisForLFunctions.HTGeometry.EventConnectionDescent

/-!
# The quadratic soldering boundary of a split event

For the split event `T : K × I → C × I`, `(k, i) ↦ (0, i)`, this file:

* classifies every pair of block endomorphisms parallel across `T`;
* proves that no endpoint map `C → K` can intertwine every independent pair of endpoint
  endomorphisms unless it is zero;
* constructs the length-two endpoint bridge `C → I → K`;
* proves that the intermediate endomorphism cancels exactly from its covariant defect;
* proves that an invertible covariantly constant composite locks the endpoint endomorphisms by
  conjugacy.

These are unconditional linear-algebra statements. The names "channel" and "solder" record their
intended role in the event-interface research program. No spacetime, gauge force, connection on a
manifold, gravity equation, or physical interpretation is assumed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R K I C : Type*}
variable [CommRing R]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup I] [Module R I]
variable [AddCommGroup C] [Module R C]

/-- General block endomorphism of the source `K × I`. -/
def splitSourceBlockEnd
    (a : Module.End R K) (b : I →ₗ[R] K)
    (c : K →ₗ[R] I) (d : Module.End R I) :
    Module.End R (K × I) where
  toFun x := (a x.1 + b x.2, c x.1 + d x.2)
  map_add' x y := by ext <;> simp <;> abel
  map_smul' r x := by ext <;> simp

/-- General block endomorphism of the target `C × I`. -/
def splitTargetBlockEnd
    (p : Module.End R C) (q : I →ₗ[R] C)
    (r : C →ₗ[R] I) (s : Module.End R I) :
    Module.End R (C × I) where
  toFun x := (p x.1 + q x.2, r x.1 + s x.2)
  map_add' x y := by ext <;> simp <;> abel
  map_smul' t x := by ext <;> simp

/--
Complete block classification for a split event. Parallelism kills the two blocks that point
against the event, identifies the transmitted endomorphisms, and leaves both endpoint
endomorphisms and both one-way off-diagonal channels arbitrary.
-/
theorem splitEventMap_block_parallel_iff
    (a : Module.End R K) (b : I →ₗ[R] K)
    (c : K →ₗ[R] I) (d : Module.End R I)
    (p : Module.End R C) (q : I →ₗ[R] C)
    (r : C →ₗ[R] I) (s : Module.End R I) :
    EventParallel (splitEventMap (R := R) (K := K) (I := I) (C := C))
        (splitSourceBlockEnd a b c d) (splitTargetBlockEnd p q r s) ↔
      c = 0 ∧ q = 0 ∧ s = d := by
  constructor
  · intro h
    have hc : c = 0 := by
      ext k
      have hk := congrArg Prod.snd (h (k, 0))
      simpa [splitEventMap, splitSourceBlockEnd, splitTargetBlockEnd] using hk.symm
    have hq : q = 0 := by
      ext i
      have hi := congrArg Prod.fst (h (0, i))
      simpa [splitEventMap, splitSourceBlockEnd, splitTargetBlockEnd] using hi
    have hs : s = d := by
      ext i
      have hi := congrArg Prod.snd (h (0, i))
      simpa [splitEventMap, splitSourceBlockEnd, splitTargetBlockEnd] using hi
    exact ⟨hc, hq, hs⟩
  · rintro ⟨rfl, rfl, rfl⟩ ⟨k, i⟩
    ext <;> simp [splitEventMap, splitSourceBlockEnd, splitTargetBlockEnd]

/--
No map between the two endpoint sectors can be canonical under completely independent endpoint
endomorphisms: a map that intertwines every pair is zero.
-/
theorem universal_endpoint_solder_eq_zero
    (η : C →ₗ[R] K)
    (h : ∀ (a : Module.End R K) (p : Module.End R C),
      a.comp η = η.comp p) :
    η = 0 := by
  simpa using (h (0 : Module.End R K) LinearMap.id).symm

/-- Length-two endpoint bridge formed from the two one-way split-event channels. -/
def splitQuadraticSolder (b : I →ₗ[R] K) (r : C →ₗ[R] I) : C →ₗ[R] K :=
  b.comp r

/-- Covariant defect of the channel from the transmitted sector to the killed sector. -/
def leftChannelCovariantDefect
    (a : Module.End R K) (d : Module.End R I) (b : I →ₗ[R] K) :
    I →ₗ[R] K :=
  a.comp b - b.comp d

/-- Covariant defect of the channel from the outgoing sector to the transmitted sector. -/
def rightChannelCovariantDefect
    (d : Module.End R I) (p : Module.End R C) (r : C →ₗ[R] I) :
    C →ₗ[R] I :=
  d.comp r - r.comp p

/--
Quadratic transmitted-channel cancellation law. The intermediate endomorphism occurs with
opposite signs in the two channel defects and disappears from the defect of their composite.
-/
theorem splitQuadraticSolder_covariant_cancellation
    (a : Module.End R K) (d : Module.End R I) (p : Module.End R C)
    (b : I →ₗ[R] K) (r : C →ₗ[R] I) :
    (leftChannelCovariantDefect a d b).comp r +
        b.comp (rightChannelCovariantDefect d p r) =
      a.comp (splitQuadraticSolder b r) -
        (splitQuadraticSolder b r).comp p := by
  ext x
  simp [leftChannelCovariantDefect, rightChannelCovariantDefect,
    splitQuadraticSolder]

/-- Covariantly constant component channels have a covariantly constant quadratic composite. -/
theorem splitQuadraticSolder_parallel_of_channels
    (a : Module.End R K) (d : Module.End R I) (p : Module.End R C)
    (b : I →ₗ[R] K) (r : C →ₗ[R] I)
    (hb : a.comp b = b.comp d) (hr : d.comp r = r.comp p) :
    a.comp (splitQuadraticSolder b r) =
      (splitQuadraticSolder b r).comp p := by
  ext x
  change a (b (r x)) = b (r (p x))
  have hbx := congrArg (fun f : I →ₗ[R] K => f (r x)) hb
  have hrx := congrArg (fun f : C →ₗ[R] I => f x) hr
  simp only [LinearMap.comp_apply] at hbx hrx
  exact hbx.trans (congrArg b hrx)

/--
If the quadratic bridge is invertible, covariant constancy locks the two endpoint endomorphisms
by conjugacy.
-/
theorem splitQuadraticSolder_equiv_locks_endpoints
    (a : Module.End R K) (d : Module.End R I) (p : Module.End R C)
    (b : I →ₗ[R] K) (r : C →ₗ[R] I) (η : C ≃ₗ[R] K)
    (hη : splitQuadraticSolder b r = η.toLinearMap)
    (hb : a.comp b = b.comp d) (hr : d.comp r = r.comp p) :
    a = η.toLinearMap.comp (p.comp η.symm.toLinearMap) := by
  apply parallel_equiv_forces_target η p a
  intro x
  have hparallel :=
    LinearMap.congr_fun (splitQuadraticSolder_parallel_of_channels a d p b r hb hr) x
  simpa [hη] using hparallel

end GaloisForLFunctions.HTGeometry
