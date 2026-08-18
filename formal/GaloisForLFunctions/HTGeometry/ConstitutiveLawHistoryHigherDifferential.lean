import GaloisForLFunctions.HTGeometry.ConstitutiveLawHistoryDifferential

/-!
# Higher law-history transgression

For an incoming law `a`, an interval transport `p`, and a later law `q`, this module constructs
the canonical higher differential from classes erased by `q` after transport through `p` to the
earlier secondary cokernel.  Its kernel and cokernel are exactly the next kernel and cokernel
survivors.  This is the page-derivation mechanism of the finite law-history spectral machine.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w x y

variable {k : Type u} {X : Type v} {Y : Type w} {Z : Type x} {W : Type y}
variable [Field k]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup Y] [Module k Y]
variable [AddCommGroup Z] [Module k Z]
variable [AddCommGroup W] [Module k W]

/-- Later-kernel classes which have survived through the current interval transport. -/
def higherKernelSource (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) : Submodule k Z :=
  LinearMap.ker q ⊓ LinearMap.range p

/-- The canonical inclusion of a surviving later-kernel class into the range of the interval. -/
def higherKernelSourceToRange (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    higherKernelSource p q →ₗ[k] LinearMap.range p where
  toFun z := ⟨z.1, z.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_le_secondaryCarrierSubmodule
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) :
    LinearMap.ker p ≤ secondaryCarrierSubmodule a p :=
  le_sup_right

/-- Quotienting first by the interval kernel and then by the incoming range. -/
def intervalKerToSecondary (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) :
    (Y ⧸ LinearMap.ker p) →ₗ[k] (Y ⧸ secondaryCarrierSubmodule a p) :=
  Submodule.factor (ker_le_secondaryCarrierSubmodule a p)

/-- Page-`r` law-history differential in interval form. -/
def higherLawHistoryDifferential
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    higherKernelSource p q →ₗ[k] (Y ⧸ secondaryCarrierSubmodule a p) :=
  (intervalKerToSecondary a p).comp
    (p.quotKerEquivRange.symm.toLinearMap.comp (higherKernelSourceToRange p q))

@[simp]
theorem higherLawHistoryDifferential_image
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W)
    (z : Y) (hz : q (p z) = 0) :
    higherLawHistoryDifferential a p q
        ⟨p z, ⟨LinearMap.mem_ker.mpr hz, ⟨z, rfl⟩⟩⟩ =
      (secondaryCarrierSubmodule a p).mkQ z := by
  change intervalKerToSecondary a p
      (p.quotKerEquivRange.symm ⟨p z, ⟨z, rfl⟩⟩) =
    (secondaryCarrierSubmodule a p).mkQ z
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  exact Submodule.factor_mk (ker_le_secondaryCarrierSubmodule a p) z

/-- The next kernel survivor: it was already produced by the incoming law before interval
transport. -/
def nextHigherKernelSource
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) : Submodule k Z :=
  LinearMap.ker q ⊓ LinearMap.range (p.comp a)

theorem nextHigherKernelSource_le
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    nextHigherKernelSource a p q ≤ higherKernelSource p q := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  obtain ⟨x, hx⟩ := hz.2
  exact ⟨a x, by simpa only [LinearMap.comp_apply] using hx⟩

def nextHigherKernelInclusion
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    nextHigherKernelSource a p q →ₗ[k] higherKernelSource p q :=
  Submodule.inclusion (nextHigherKernelSource_le a p q)

theorem range_nextHigherKernelInclusion_eq_ker
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    LinearMap.range (nextHigherKernelInclusion a p q) =
      LinearMap.ker (higherLawHistoryDifferential a p q) := by
  ext z
  constructor
  · rintro ⟨z', rfl⟩
    rw [LinearMap.mem_ker]
    obtain ⟨x, hx⟩ := z'.2.2
    have hzval : z'.1 = p (a x) := by
      simpa only [LinearMap.comp_apply] using hx.symm
    have hqpa : q (p (a x)) = 0 := by
      rw [← hzval]
      exact LinearMap.mem_ker.mp z'.2.1
    have heq : nextHigherKernelInclusion a p q z' =
        (⟨p (a x), ⟨LinearMap.mem_ker.mpr hqpa, ⟨a x, rfl⟩⟩⟩ : higherKernelSource p q) :=
      Subtype.ext hzval
    rw [heq, higherLawHistoryDifferential_image a p q (a x) hqpa,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_left ⟨x, rfl⟩
  · intro hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨y, hy⟩ := z.2.2
    have hqpy : q (p y) = 0 := by
      calc
        q (p y) = q z.1 := congrArg q hy
        _ = 0 := LinearMap.mem_ker.mp z.2.1
    have hz' : z = ⟨p y, ⟨LinearMap.mem_ker.mpr hqpy, ⟨y, rfl⟩⟩⟩ := by
      exact Subtype.ext hy.symm
    have hymem : y ∈ secondaryCarrierSubmodule a p := by
      rw [← Submodule.Quotient.mk_eq_zero]
      rw [← Submodule.mkQ_apply]
      rw [← higherLawHistoryDifferential_image a p q y hqpy]
      simpa only [hz'] using hz
    rw [secondaryCarrierSubmodule, Submodule.mem_sup] at hymem
    obtain ⟨u, ⟨x, hx⟩, n, hn, hun⟩ := hymem
    have hval : p y = p (a x) := by
      rw [← hx] at hun
      have := congrArg p hun
      simpa [map_add, LinearMap.mem_ker.mp hn] using this.symm
    let znext : nextHigherKernelSource a p q := ⟨z.1, ⟨z.2.1, ⟨x, by
      change p (a x) = z.1
      calc
        p (a x) = p y := hval.symm
        _ = z.1 := hy⟩⟩⟩
    refine ⟨znext, ?_⟩
    exact Subtype.ext rfl

theorem currentSecondary_le_next
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    secondaryCarrierSubmodule a p ≤ secondaryCarrierSubmodule a (q.comp p) := by
  rw [secondaryCarrierSubmodule, secondaryCarrierSubmodule]
  apply sup_le_sup_left
  intro y hy
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp hy, map_zero]

/-- Passage from the current cokernel survivor to the next one. -/
def higherCokerTransition
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    (Y ⧸ secondaryCarrierSubmodule a p) →ₗ[k]
      (Y ⧸ secondaryCarrierSubmodule a (q.comp p)) :=
  Submodule.factor (currentSecondary_le_next a p q)

@[simp]
theorem higherCokerTransition_mkQ
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) (y : Y) :
    higherCokerTransition a p q ((secondaryCarrierSubmodule a p).mkQ y) =
      (secondaryCarrierSubmodule a (q.comp p)).mkQ y :=
  Submodule.factor_mk (currentSecondary_le_next a p q) y

theorem range_higherLawHistoryDifferential_eq_ker_transition
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    LinearMap.range (higherLawHistoryDifferential a p q) =
      LinearMap.ker (higherCokerTransition a p q) := by
  ext c
  constructor
  · rintro ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    obtain ⟨y, hy⟩ := z.2.2
    have hqpy : q (p y) = 0 := by
      calc
        q (p y) = q z.1 := congrArg q hy
        _ = 0 := LinearMap.mem_ker.mp z.2.1
    have hz' : z = ⟨p y, ⟨LinearMap.mem_ker.mpr hqpy, ⟨y, rfl⟩⟩⟩ :=
      Subtype.ext hy.symm
    rw [hz', higherLawHistoryDifferential_image a p q y hqpy,
      higherCokerTransition_mkQ,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right (LinearMap.mem_ker.mpr hqpy)
  · intro hc
    induction c using Submodule.Quotient.induction_on with | _ y => ?_
    change higherCokerTransition a p q ((secondaryCarrierSubmodule a p).mkQ y) = 0 at hc
    rw [higherCokerTransition_mkQ, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, secondaryCarrierSubmodule, Submodule.mem_sup] at hc
    obtain ⟨u, ⟨x, hx⟩, n, hn, hun⟩ := hc
    have hqpn : q (p n) = 0 := LinearMap.mem_ker.mp hn
    let z : higherKernelSource p q :=
      ⟨p n, ⟨LinearMap.mem_ker.mpr hqpn, ⟨n, rfl⟩⟩⟩
    refine ⟨z, ?_⟩
    rw [higherLawHistoryDifferential_image a p q n hqpn]
    change (secondaryCarrierSubmodule a p).mkQ n =
      (secondaryCarrierSubmodule a p).mkQ y
    apply (Submodule.Quotient.eq _).2
    rw [← hun, ← hx]
    change n - (a x + n) ∈ secondaryCarrierSubmodule a p
    have : n - (a x + n) = -(a x) := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩)

theorem higherCokerTransition_surjective
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    Function.Surjective (higherCokerTransition a p q) :=
  Submodule.factor_surjective (currentSecondary_le_next a p q)

/-- Cokernel of the current higher differential is canonically the next cokernel survivor. -/
def higherDifferentialCokerEquivNext
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    ((Y ⧸ secondaryCarrierSubmodule a p) ⧸
        LinearMap.range (higherLawHistoryDifferential a p q)) ≃ₗ[k]
      (Y ⧸ secondaryCarrierSubmodule a (q.comp p)) :=
  (Submodule.quotEquivOfEq _ _
      (range_higherLawHistoryDifferential_eq_ker_transition a p q)).trans
    ((higherCokerTransition a p q).quotKerEquivRange.trans
      (LinearEquiv.ofTop _
        (LinearMap.range_eq_top.mpr (higherCokerTransition_surjective a p q))))

/-- Exact page derivation: current higher transgression has precisely the next kernel survivor as
kernel and the next cokernel survivor as cokernel. -/
theorem higherLawHistory_page_derivation
    (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    LinearMap.range (nextHigherKernelInclusion a p q) =
        LinearMap.ker (higherLawHistoryDifferential a p q) ∧
      LinearMap.range (higherLawHistoryDifferential a p q) =
        LinearMap.ker (higherCokerTransition a p q) ∧
      Function.Surjective (higherCokerTransition a p q) ∧
      Nonempty (((Y ⧸ secondaryCarrierSubmodule a p) ⧸
          LinearMap.range (higherLawHistoryDifferential a p q)) ≃ₗ[k]
        (Y ⧸ secondaryCarrierSubmodule a (q.comp p))) :=
  ⟨range_nextHigherKernelInclusion_eq_ker a p q,
    range_higherLawHistoryDifferential_eq_ker_transition a p q,
    higherCokerTransition_surjective a p q,
    ⟨higherDifferentialCokerEquivNext a p q⟩⟩

end

end GaloisForLFunctions.HTGeometry
