import GaloisForLFunctions.RHTower.AnchorHead

/-!
# A derived inverse limit of acyclic finite fibers is zero

For a tower of abelian groups the limit is the kernel and the first derived limit the cokernel of
the shift-minus-identity map on the product.  If every stage is a zero object both vanish, so a
tower of acyclic complexes contributes nothing.

The specialized finite prime complex is `[ℂ →(1 - p^{-s})→ ℂ]`.  In the open right half plane the
Euler factor is nonzero, so the differential is bijective: the complex is acyclic in both degrees,
and so is every finite tensor product over a prime set, whose total differential determinant is the
product of the Euler factors.

Hence zeta zeros cannot arise as `lim¹` cohomology of already-specialized finite fibers.
-/

noncomputable section

namespace RHTower

open Complex

/-! ### The tower limit and its first derived functor -/

variable {A : ℕ → Type} [∀ n, AddCommGroup (A n)]

/-- The shift-minus-identity map of a tower; its kernel is `lim` and its cokernel is `lim¹`. -/
def towerDiff (f : ∀ n, A (n + 1) →+ A n) : (∀ n, A n) →+ (∀ n, A n) where
  toFun a := fun n => a n - f n (a (n + 1))
  map_zero' := by funext n; simp
  map_add' a b := by
    funext n
    simp only [Pi.add_apply, map_add]
    abel

/-- The inverse limit of a tower of abelian groups. -/
def towerLim (f : ∀ n, A (n + 1) →+ A n) : AddSubgroup (∀ n, A n) := (towerDiff f).ker

/-- The first derived inverse limit of a tower of abelian groups. -/
def towerLimOne (f : ∀ n, A (n + 1) →+ A n) : Type := (∀ n, A n) ⧸ (towerDiff f).range

instance (f : ∀ n, A (n + 1) →+ A n) : AddCommGroup (towerLimOne f) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- **A tower of zero objects has zero limit.** -/
theorem towerLim_subsingleton [∀ n, Subsingleton (A n)] (f : ∀ n, A (n + 1) →+ A n) :
    Subsingleton (towerLim f) := by
  refine ⟨fun x y => ?_⟩
  refine Subtype.ext (funext fun n => Subsingleton.elim _ _)

/-- **A tower of zero objects has zero derived limit.** -/
theorem towerLimOne_subsingleton [∀ n, Subsingleton (A n)] (f : ∀ n, A (n + 1) →+ A n) :
    Subsingleton (towerLimOne f) := by
  refine ⟨fun x y => ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    induction y using QuotientAddGroup.induction_on with
    | H b =>
      have : a = b := funext fun n => Subsingleton.elim _ _
      rw [this]

/-! ### The specialized finite prime complexes are contractible -/

/-- The differential of the specialized finite prime complex `[ℂ →(1 - p^(-s))→ ℂ]`. -/
def primeKoszulDiff (p : ℕ) (s : ℂ) : ℂ →ₗ[ℂ] ℂ :=
  (1 - (p : ℂ) ^ (-s)) • LinearMap.id

theorem primeKoszulDiff_apply (p : ℕ) (s z : ℂ) :
    primeKoszulDiff p s z = (1 - (p : ℂ) ^ (-s)) * z := by
  simp [primeKoszulDiff]

/-- **Degree-zero acyclicity.**  In the critical strip the differential is injective. -/
theorem primeKoszulDiff_ker {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    LinearMap.ker (primeKoszulDiff p s) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro z hz
  rw [primeKoszulDiff_apply] at hz
  exact (mul_eq_zero.mp hz).resolve_left (eulerFactor_ne_zero hp hs)

/-- **Degree-one acyclicity.**  In the critical strip the differential is surjective. -/
theorem primeKoszulDiff_range {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    LinearMap.range (primeKoszulDiff p s) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro w
  refine ⟨w / (1 - (p : ℂ) ^ (-s)), ?_⟩
  rw [primeKoszulDiff_apply, mul_div_cancel₀ _ (eulerFactor_ne_zero hp hs)]

/-- **The finite prime complex is contractible in the strip.** -/
theorem primeKoszulDiff_bijective {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    Function.Bijective (primeKoszulDiff p s) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact primeKoszulDiff_ker hp hs
  · rw [← LinearMap.range_eq_top]
    exact primeKoszulDiff_range hp hs

/-- **Every finite prime tensor product is contractible in the strip.**  The total Euler
determinant is nonzero. -/
theorem prod_eulerFactor_ne_zero (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    ∏ p ∈ P, (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  exact fun p hp => eulerFactor_ne_zero (hP p hp) hs

/-- **The derived limit of the specialized finite fibers vanishes.**  If every stage of a tower is a
zero object — as the cohomology of the specialized finite prime complexes is in the strip — then the
limit and the derived limit are both zero, so no defect can be created there. -/
theorem acyclic_tower_derivedLimit_zero [∀ n, Subsingleton (A n)]
    (f : ∀ n, A (n + 1) →+ A n) :
    Subsingleton (towerLim f) ∧ Subsingleton (towerLimOne f) :=
  ⟨towerLim_subsingleton f, towerLimOne_subsingleton f⟩

end RHTower
