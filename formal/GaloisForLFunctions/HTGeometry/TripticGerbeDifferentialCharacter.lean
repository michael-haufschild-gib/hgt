import GaloisForLFunctions.HTGeometry.GammaGerbeDixmierDouadyGenerator

/-!
# The differential-character comparison in degree two

A gerbe cochain on the triptic lattice carries three pieces of data: its coboundary — the curvature,
or in integral form the Dixmier–Douady cocycle — the class of the cochain itself, and the holonomy,
read off on the standard basis.  The comparison statement is that the first two determine the
cochain up to a *flat character*, and the third removes that ambiguity.

Concretely: the difference of two cochains with the same coboundary is a `2`-cocycle, and its
class is detected by the commutator pairing `B(a, b) = c a b - c b a`.  That pairing is
bi-additive and alternating — the commutator of the central extension the cocycle defines — so it
is determined by its values on the three basis pairs.  When those vanish the cocycle is symmetric,
the extension it defines is abelian, the lattice is free, so the extension splits and the cocycle
is a coboundary.

* `cocycleCommutator`, `cocycleCommutator_add_left`, `cocycleCommutator_eq_zero_of_basis`;
* `exists_coboundary₁_of_symm` — a symmetric `2`-cocycle is a coboundary;
* `exists_coboundary₁_of_cocycle_of_basis` — the vanishing of the three basis commutators suffices;
* `exists_coboundary₁_iff_basis` — the three basis commutators are a complete obstruction;
* `eq_add_coboundary₁_of_coboundary₂_eq_of_basis` — the comparison, for a trivial action;
* `twistedCoboundary₁`, `twistedCoboundary₂`, `exists_twistedCoboundary₁_of_flat_of_basis`;
* `eq_add_twistedCoboundary₁_of_curvature_of_flat_of_holonomy` — **the differential-character
  comparison** for a gerbe cochain with a lattice action on the coefficients;
* `eq_add_twistedCoboundary₁_of_gammaGerbeDD` — the same, with the curvature fixed to the
  Dixmier–Douady cocycle of the gamma gerbe.
-/

noncomputable section

namespace GaloisForLFunctions

namespace GerbeCharacteristic

variable {M : Type*} [AddCommGroup M]

/-! ### The cocycle identity -/

/-- The `2`-cocycle identity, in the form used below. -/
theorem cocycle_apply {c : TripticLattice → TripticLattice → M} (hc : coboundary₂ c = 0)
    (a b d : TripticLattice) : c (a + b) d + c a b = c b d + c a (b + d) := by
  have h := congrFun (congrFun (congrFun hc a) b) d
  simp only [coboundary₂, Pi.zero_apply] at h
  have h2 : c (a + b) d + c a b - (c b d + c a (b + d))
      = -(c b d - c (a + b) d + c a (b + d) - c a b) := by abel
  rw [h, neg_zero, sub_eq_zero] at h2
  exact h2

theorem cocycle_zero_left {c : TripticLattice → TripticLattice → M} (hc : coboundary₂ c = 0)
    (d : TripticLattice) : c 0 d = c 0 0 := by
  have h := cocycle_apply hc 0 0 d
  rw [add_zero, zero_add] at h
  exact (add_left_cancel h).symm

theorem cocycle_zero_right {c : TripticLattice → TripticLattice → M} (hc : coboundary₂ c = 0)
    (a : TripticLattice) : c a 0 = c 0 0 := by
  have h := cocycle_apply hc a 0 0
  rw [add_zero, add_zero] at h
  exact add_right_cancel h

/-! ### The commutator pairing -/

/-- The commutator pairing of a `2`-cochain. -/
def cocycleCommutator (c : TripticLattice → TripticLattice → M) :
    TripticLattice → TripticLattice → M :=
  fun a b => c a b - c b a

theorem cocycleCommutator_swap (c : TripticLattice → TripticLattice → M) (a b : TripticLattice) :
    cocycleCommutator c a b = -cocycleCommutator c b a := by
  simp only [cocycleCommutator]
  abel

/-- **The commutator pairing of a `2`-cocycle is additive in its first argument.** -/
theorem cocycleCommutator_add_left {c : TripticLattice → TripticLattice → M}
    (hc : coboundary₂ c = 0) (a b d : TripticLattice) :
    cocycleCommutator c (a + b) d = cocycleCommutator c a d + cocycleCommutator c b d := by
  have h1 := cocycle_apply hc a b d
  have h2 := cocycle_apply hc d a b
  have h3 := cocycle_apply hc a d b
  rw [add_comm b d] at h1
  rw [add_comm d a] at h2
  have e1 : c (a + b) d = c b d + c a (d + b) - c a b := eq_sub_of_add_eq h1
  have e2 : c d (a + b) = c (a + d) b + c d a - c a b := eq_sub_of_add_eq' h2.symm
  have e3 : c a (d + b) = c (a + d) b + c a d - c d b := eq_sub_of_add_eq' h3.symm
  simp only [cocycleCommutator]
  rw [e1, e2, e3]
  abel

theorem cocycleCommutator_zero_left {c : TripticLattice → TripticLattice → M}
    (hc : coboundary₂ c = 0) (d : TripticLattice) : cocycleCommutator c 0 d = 0 := by
  simp only [cocycleCommutator, cocycle_zero_left hc, cocycle_zero_right hc, sub_self]

/-- The commutator pairing as an additive map in its first argument. -/
def cocycleCommutatorHom {c : TripticLattice → TripticLattice → M} (hc : coboundary₂ c = 0)
    (d : TripticLattice) : TripticLattice →+ M :=
  AddMonoidHom.mk' (fun a => cocycleCommutator c a d)
    (fun a b => cocycleCommutator_add_left hc a b d)

@[simp] theorem cocycleCommutatorHom_apply {c : TripticLattice → TripticLattice → M}
    (hc : coboundary₂ c = 0) (d a : TripticLattice) :
    cocycleCommutatorHom hc d a = cocycleCommutator c a d := rfl

/-- The standard basis expansion of a lattice vector. -/
theorem sum_zsmul_basisVec (a : TripticLattice) :
    ∑ i : Fin 3, (a i) • basisVec i = a := by
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
    rw [basisVec, ← Pi.single_smul, smul_eq_mul, mul_one])]
  exact Finset.univ_sum_single a

/-- **The commutator pairing is determined by the three basis pairs.** -/
theorem cocycleCommutator_eq_zero_of_basis {c : TripticLattice → TripticLattice → M}
    (hc : coboundary₂ c = 0)
    (hbasis : ∀ i j : Fin 3, cocycleCommutator c (basisVec i) (basisVec j) = 0)
    (a b : TripticLattice) : cocycleCommutator c a b = 0 := by
  have hcol : ∀ (i : Fin 3) (y : TripticLattice), cocycleCommutator c (basisVec i) y = 0 := by
    intro i y
    have hswap : cocycleCommutator c (basisVec i) y = -cocycleCommutator c y (basisVec i) :=
      cocycleCommutator_swap c _ _
    have hy : cocycleCommutator c y (basisVec i) = 0 := by
      have hsum := congrArg (cocycleCommutatorHom hc (basisVec i)) (sum_zsmul_basisVec y)
      rw [map_sum] at hsum
      have hzero : ∑ j : Fin 3, (cocycleCommutatorHom hc (basisVec i)) (y j • basisVec j) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          rw [map_zsmul, cocycleCommutatorHom_apply, hbasis j i, smul_zero]
      rw [hzero] at hsum
      exact hsum.symm
    rw [hswap, hy, neg_zero]
  have hsum := congrArg (cocycleCommutatorHom hc b) (sum_zsmul_basisVec a)
  rw [map_sum] at hsum
  have hzero : ∑ j : Fin 3, (cocycleCommutatorHom hc b) (a j • basisVec j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [map_zsmul, cocycleCommutatorHom_apply, hcol j b, smul_zero]
  rw [hzero] at hsum
  exact hsum.symm

/-! ### A symmetric cocycle is a coboundary -/

/-- The hypotheses making the twisted product on `M × Λ` an abelian group. -/
class IsSymmNormalCocycle (c : TripticLattice → TripticLattice → M) : Prop where
  cocycle : coboundary₂ c = 0
  symm : ∀ a b, c a b = c b a
  zero : c 0 0 = 0

/-- The central extension of the triptic lattice defined by a `2`-cochain. -/
structure CocycleExt (c : TripticLattice → TripticLattice → M) where
  /-- The coefficient part. -/
  val : M
  /-- The lattice part. -/
  base : TripticLattice

namespace CocycleExt

variable {c : TripticLattice → TripticLattice → M}

omit [AddCommGroup M] in
@[ext] theorem ext {x y : CocycleExt c} (hv : x.val = y.val) (hb : x.base = y.base) : x = y := by
  cases x
  cases y
  simp_all

instance : Add (CocycleExt c) :=
  ⟨fun x y => ⟨x.val + y.val + c x.base y.base, x.base + y.base⟩⟩

instance : Zero (CocycleExt c) := ⟨⟨0, 0⟩⟩

instance : Neg (CocycleExt c) :=
  ⟨fun x => ⟨-x.val - c x.base (-x.base), -x.base⟩⟩

instance [IsSymmNormalCocycle c] : AddCommGroup (CocycleExt c) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc x y z := by
    refine ext ?_ (add_assoc _ _ _)
    show x.val + y.val + c x.base y.base + z.val + c (x.base + y.base) z.base
      = x.val + (y.val + z.val + c y.base z.base) + c x.base (y.base + z.base)
    have h := cocycle_apply (IsSymmNormalCocycle.cocycle (c := c)) x.base y.base z.base
    have hgoal : x.val + y.val + c x.base y.base + z.val + c (x.base + y.base) z.base
        - (x.val + (y.val + z.val + c y.base z.base) + c x.base (y.base + z.base))
        = (c (x.base + y.base) z.base + c x.base y.base)
          - (c y.base z.base + c x.base (y.base + z.base)) := by abel
    rw [h, sub_self, sub_eq_zero] at hgoal
    exact hgoal
  zero_add x := by
    refine ext ?_ (zero_add _)
    show (0 : M) + x.val + c 0 x.base = x.val
    rw [cocycle_zero_left (IsSymmNormalCocycle.cocycle (c := c)),
      IsSymmNormalCocycle.zero (c := c), zero_add, add_zero]
  add_zero x := by
    refine ext ?_ (add_zero _)
    show x.val + 0 + c x.base 0 = x.val
    rw [cocycle_zero_right (IsSymmNormalCocycle.cocycle (c := c)),
      IsSymmNormalCocycle.zero (c := c), add_zero, add_zero]
  neg_add_cancel x := by
    refine ext ?_ (neg_add_cancel _)
    show -x.val - c x.base (-x.base) + x.val + c (-x.base) x.base = (0 : M)
    rw [IsSymmNormalCocycle.symm (c := c) (-x.base) x.base]
    abel
  add_comm x y := by
    refine ext ?_ (add_comm _ _)
    show x.val + y.val + c x.base y.base = y.val + x.val + c y.base x.base
    rw [IsSymmNormalCocycle.symm (c := c) x.base y.base]
    abel

@[simp] theorem add_val [IsSymmNormalCocycle c] (x y : CocycleExt c) :
    (x + y).val = x.val + y.val + c x.base y.base := rfl

@[simp] theorem add_base [IsSymmNormalCocycle c] (x y : CocycleExt c) :
    (x + y).base = x.base + y.base := rfl

/-- The lattice component of the extension. -/
def baseHom (c : TripticLattice → TripticLattice → M) [IsSymmNormalCocycle c] :
    CocycleExt c →+ TripticLattice where
  toFun x := x.base
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical lift of a basis vector. -/
def unitLift (c : TripticLattice → TripticLattice → M) [IsSymmNormalCocycle c] (i : Fin 3) :
    CocycleExt c :=
  ⟨0, basisVec i⟩

/-- The splitting of the extension, from freeness of the lattice. -/
def split (c : TripticLattice → TripticLattice → M) [IsSymmNormalCocycle c]
    (a : TripticLattice) : CocycleExt c :=
  ∑ i : Fin 3, (a i) • unitLift c i

theorem split_add [IsSymmNormalCocycle c] (a b : TripticLattice) :
    split c (a + b) = split c a + split c b := by
  simp only [split, Pi.add_apply, add_zsmul]
  exact Finset.sum_add_distrib

theorem base_split [IsSymmNormalCocycle c] (a : TripticLattice) : (split c a).base = a := by
  have hsum := map_sum (baseHom c) (fun i => (a i) • unitLift c i) Finset.univ
  have hterm : ∀ i : Fin 3, (baseHom c) ((a i) • unitLift c i) = (a i) • basisVec i := by
    intro i
    rw [map_zsmul]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i, sum_zsmul_basisVec] at hsum
  exact hsum

end CocycleExt

theorem coboundary₁_add (h₁ h₂ : TripticLattice → M) :
    coboundary₁ (fun x => h₁ x + h₂ x) = fun a b => coboundary₁ h₁ a b + coboundary₁ h₂ a b := by
  funext a b
  simp only [coboundary₁]
  abel

/-- **A symmetric `2`-cocycle on the triptic lattice is a coboundary.**  The twisted product it
defines is an abelian group, and the lattice is free, so the extension splits. -/
theorem exists_coboundary₁_of_symm {c : TripticLattice → TripticLattice → M}
    (hc : coboundary₂ c = 0) (hsym : ∀ a b, c a b = c b a) :
    ∃ h : TripticLattice → M, c = coboundary₁ h := by
  set k : M := c 0 0 with hk
  set c' : TripticLattice → TripticLattice → M := fun a b => c a b - k with hc'
  have hc'cocycle : coboundary₂ c' = 0 := by
    funext a b d
    have h := congrFun (congrFun (congrFun hc a) b) d
    simp only [coboundary₂, Pi.zero_apply, hc'] at h ⊢
    have key : c b d - k - (c (a + b) d - k) + (c a (b + d) - k) - (c a b - k)
        = c b d - c (a + b) d + c a (b + d) - c a b := by abel
    rw [key, h]
  haveI : IsSymmNormalCocycle c' :=
    { cocycle := hc'cocycle
      symm := fun a b => by simp only [hc', hsym a b]
      zero := by simp only [hc', hk, sub_self] }
  refine ⟨fun x => -(CocycleExt.split c' x).val + k, ?_⟩
  funext a b
  have hsplit := CocycleExt.split_add (c := c') a b
  have hval := congrArg CocycleExt.val hsplit
  rw [CocycleExt.add_val, CocycleExt.base_split, CocycleExt.base_split] at hval
  have hc'ab : c' a b = (CocycleExt.split c' (a + b)).val - (CocycleExt.split c' a).val
      - (CocycleExt.split c' b).val := by
    rw [hval]
    abel
  simp only [coboundary₁]
  have hgoal : -(CocycleExt.split c' b).val + k - (-(CocycleExt.split c' (a + b)).val + k)
      + (-(CocycleExt.split c' a).val + k)
      = ((CocycleExt.split c' (a + b)).val - (CocycleExt.split c' a).val
        - (CocycleExt.split c' b).val) + k := by abel
  rw [hgoal, ← hc'ab, hc']
  simp

/-- **A `2`-cocycle whose three basis commutators vanish is a coboundary.** -/
theorem exists_coboundary₁_of_cocycle_of_basis {c : TripticLattice → TripticLattice → M}
    (hc : coboundary₂ c = 0)
    (hbasis : ∀ i j : Fin 3, cocycleCommutator c (basisVec i) (basisVec j) = 0) :
    ∃ h : TripticLattice → M, c = coboundary₁ h := by
  refine exists_coboundary₁_of_symm hc fun a b => ?_
  have h := cocycleCommutator_eq_zero_of_basis hc hbasis a b
  simpa only [cocycleCommutator, sub_eq_zero] using h

theorem cocycleCommutator_coboundary₁ (h : TripticLattice → M) (a b : TripticLattice) :
    cocycleCommutator (coboundary₁ h) a b = 0 := by
  simp only [cocycleCommutator, coboundary₁, add_comm a b]
  abel

/-- **The commutator pairing on the three basis pairs is a complete obstruction.** -/
theorem exists_coboundary₁_iff_basis {c : TripticLattice → TripticLattice → M}
    (hc : coboundary₂ c = 0) :
    (∃ h : TripticLattice → M, c = coboundary₁ h)
      ↔ ∀ i j : Fin 3, cocycleCommutator c (basisVec i) (basisVec j) = 0 := by
  refine ⟨fun ⟨h, hh⟩ i j => ?_, exists_coboundary₁_of_cocycle_of_basis hc⟩
  rw [hh]
  exact cocycleCommutator_coboundary₁ h _ _

/-- **The differential-character comparison.**  Two cochains with the same coboundary — the same
curvature, and in integral form the same Dixmier--Douady cocycle — and the same holonomy on the
three basis pairs differ by a coboundary, hence define the same class. -/
theorem eq_add_coboundary₁_of_coboundary₂_eq_of_basis
    {g g' : TripticLattice → TripticLattice → M}
    (hcurv : coboundary₂ g = coboundary₂ g')
    (hhol : ∀ i j : Fin 3,
      cocycleCommutator g (basisVec i) (basisVec j)
        = cocycleCommutator g' (basisVec i) (basisVec j)) :
    ∃ h : TripticLattice → M, ∀ a b, g a b = g' a b + coboundary₁ h a b := by
  have hd : coboundary₂ (fun a b => g a b - g' a b) = 0 := by
    funext a b d
    have h := congrFun (congrFun (congrFun hcurv a) b) d
    simp only [coboundary₂, Pi.zero_apply] at h ⊢
    have key : g b d - g' b d - (g (a + b) d - g' (a + b) d) + (g a (b + d) - g' a (b + d))
        - (g a b - g' a b)
        = (g b d - g (a + b) d + g a (b + d) - g a b)
          - (g' b d - g' (a + b) d + g' a (b + d) - g' a b) := by abel
    rw [key, h, sub_self]
  have hbasis : ∀ i j : Fin 3,
      cocycleCommutator (fun a b => g a b - g' a b) (basisVec i) (basisVec j) = 0 := by
    intro i j
    have h := hhol i j
    simp only [cocycleCommutator] at h ⊢
    have key : g (basisVec i) (basisVec j) - g' (basisVec i) (basisVec j)
        - (g (basisVec j) (basisVec i) - g' (basisVec j) (basisVec i))
        = (g (basisVec i) (basisVec j) - g (basisVec j) (basisVec i))
          - (g' (basisVec i) (basisVec j) - g' (basisVec j) (basisVec i)) := by abel
    rw [key, h, sub_self]
  obtain ⟨h, hh⟩ := exists_coboundary₁_of_cocycle_of_basis hd hbasis
  refine ⟨h, fun a b => ?_⟩
  have hthis := congrFun (congrFun hh a) b
  rw [← hthis]
  abel

/-! ### The twisted comparison: gauge equivalence of gerbe cochains -/

/-- The inhomogeneous `1`-coboundary for a lattice action on the coefficients. -/
def twistedCoboundary₁ (act : TripticLattice → M ≃+ M) (h : TripticLattice → M) :
    TripticLattice → TripticLattice → M :=
  fun a b => act a (h b) - h (a + b) + h a

/-- The inhomogeneous `2`-coboundary for a lattice action on the coefficients. -/
def twistedCoboundary₂ (act : TripticLattice → M ≃+ M) (g : TripticLattice → TripticLattice → M) :
    TripticLattice → TripticLattice → TripticLattice → M :=
  fun a b d => act a (g b d) - g (a + b) d + g a (b + d) - g a b

/-- **A flat cocycle whose three basis holonomies vanish is a gauge transformation.**  On the
invariants the action disappears, so the twisted complex is the untwisted one and the commutator
pairing is a complete obstruction. -/
theorem exists_twistedCoboundary₁_of_flat_of_basis
    (act : TripticLattice → M ≃+ M) (N : AddSubgroup M)
    (hN : ∀ (a : TripticLattice) (x : M), x ∈ N → act a x = x)
    {g : TripticLattice → TripticLattice → M} (hg : ∀ a b, g a b ∈ N)
    (hcocycle : twistedCoboundary₂ act g = 0)
    (hbasis : ∀ i j : Fin 3, cocycleCommutator g (basisVec i) (basisVec j) = 0) :
    ∃ h : TripticLattice → M, (∀ a, h a ∈ N) ∧ ∀ a b, g a b = twistedCoboundary₁ act h a b := by
  set G : TripticLattice → TripticLattice → N := fun a b => ⟨g a b, hg a b⟩ with hG
  have hGcocycle : coboundary₂ G = 0 := by
    funext a b d
    have h := congrFun (congrFun (congrFun hcocycle a) b) d
    simp only [twistedCoboundary₂, Pi.zero_apply, hN a (g b d) (hg b d)] at h
    apply Subtype.ext
    simpa only [coboundary₂, hG, AddSubgroup.coe_sub, AddSubgroup.coe_add,
      AddSubgroup.coe_zero, Pi.zero_apply] using h
  have hGbasis : ∀ i j : Fin 3, cocycleCommutator G (basisVec i) (basisVec j) = 0 := by
    intro i j
    apply Subtype.ext
    simpa only [cocycleCommutator, hG, AddSubgroup.coe_sub, AddSubgroup.coe_zero]
      using hbasis i j
  obtain ⟨H, hH⟩ := exists_coboundary₁_of_cocycle_of_basis hGcocycle hGbasis
  refine ⟨fun a => (H a : M), fun a => (H a).2, fun a b => ?_⟩
  have hval := congrFun (congrFun hH a) b
  have hcoe : g a b = ((coboundary₁ H a b : N) : M) := congrArg Subtype.val hval
  rw [hcoe]
  simp only [coboundary₁, twistedCoboundary₁, AddSubgroup.coe_add, AddSubgroup.coe_sub,
    hN a (H b : M) (H b).2]

/-- **The differential-character comparison.**  Two gerbe cochains with the same coboundary — the
same curvature, and in integral form the same Dixmier--Douady cocycle — whose difference is flat
and whose holonomies on the three basis pairs agree, differ by a gauge transformation, hence
define the same differential character. -/
theorem eq_add_twistedCoboundary₁_of_curvature_of_flat_of_holonomy
    (act : TripticLattice → M ≃+ M) (N : AddSubgroup M)
    (hN : ∀ (a : TripticLattice) (x : M), x ∈ N → act a x = x)
    {g g' : TripticLattice → TripticLattice → M}
    (hcurv : twistedCoboundary₂ act g = twistedCoboundary₂ act g')
    (hflat : ∀ a b, g a b - g' a b ∈ N)
    (hhol : ∀ i j : Fin 3,
      cocycleCommutator g (basisVec i) (basisVec j)
        = cocycleCommutator g' (basisVec i) (basisVec j)) :
    ∃ h : TripticLattice → M, (∀ a, h a ∈ N) ∧
      ∀ a b, g a b = g' a b + twistedCoboundary₁ act h a b := by
  have hcocycle : twistedCoboundary₂ act (fun a b => g a b - g' a b) = 0 := by
    funext a b d
    have h := congrFun (congrFun (congrFun hcurv a) b) d
    simp only [twistedCoboundary₂, Pi.zero_apply, map_sub] at h ⊢
    have key : act a (g b d) - act a (g' b d) - (g (a + b) d - g' (a + b) d)
        + (g a (b + d) - g' a (b + d)) - (g a b - g' a b)
        = (act a (g b d) - g (a + b) d + g a (b + d) - g a b)
          - (act a (g' b d) - g' (a + b) d + g' a (b + d) - g' a b) := by abel
    rw [key, h, sub_self]
  have hbasis : ∀ i j : Fin 3,
      cocycleCommutator (fun a b => g a b - g' a b) (basisVec i) (basisVec j) = 0 := by
    intro i j
    have h := hhol i j
    simp only [cocycleCommutator] at h ⊢
    have key : g (basisVec i) (basisVec j) - g' (basisVec i) (basisVec j)
        - (g (basisVec j) (basisVec i) - g' (basisVec j) (basisVec i))
        = (g (basisVec i) (basisVec j) - g (basisVec j) (basisVec i))
          - (g' (basisVec i) (basisVec j) - g' (basisVec j) (basisVec i)) := by abel
    rw [key, h, sub_self]
  obtain ⟨h, hhN, hEq⟩ :=
    exists_twistedCoboundary₁_of_flat_of_basis act N hN hflat hcocycle hbasis
  refine ⟨h, hhN, fun a b => ?_⟩
  have hab := hEq a b
  rw [← hab]
  abel

/-- **The comparison in the gamma gerbe's own shape.**  Two cochains whose twisted coboundary is the
Dixmier--Douady cocycle of the gamma gerbe — the same integral class, and with it the same
curvature — whose difference is flat and whose holonomies on the three basis pairs agree, are gauge
equivalent. -/
theorem eq_add_twistedCoboundary₁_of_gammaGerbeDD
    (act : TripticLattice → M ≃+ M) (N : AddSubgroup M)
    (hN : ∀ (a : TripticLattice) (x : M), x ∈ N → act a x = x)
    (period : ℤ →+ M) {g g' : TripticLattice → TripticLattice → M}
    (hg : twistedCoboundary₂ act g = fun a b d => period (gammaGerbeDD a b d))
    (hg' : twistedCoboundary₂ act g' = fun a b d => period (gammaGerbeDD a b d))
    (hflat : ∀ a b, g a b - g' a b ∈ N)
    (hhol : ∀ i j : Fin 3,
      cocycleCommutator g (basisVec i) (basisVec j)
        = cocycleCommutator g' (basisVec i) (basisVec j)) :
    ∃ h : TripticLattice → M, (∀ a, h a ∈ N) ∧
      ∀ a b, g a b = g' a b + twistedCoboundary₁ act h a b :=
  eq_add_twistedCoboundary₁_of_curvature_of_flat_of_holonomy act N hN (hg.trans hg'.symm) hflat hhol

end GerbeCharacteristic

end GaloisForLFunctions
