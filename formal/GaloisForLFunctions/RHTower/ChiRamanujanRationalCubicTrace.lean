import GaloisForLFunctions.RHTower.ChiRamanujanPositiveRationalTrace

/-!
# Complete positive-rational cubic trace and literal arithmetic-axis subtraction

An explicit pair equivalence carries the full signed and absolute prime-lattice
sums to all positive rational pairs with their actual Ramanujan denominator
coefficients. Arithmetic axes are removed literally. Physical prime contraction
matching and finite-height near-resonances remain separate obligations.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RHTower.BAGTrace

abbrev PositiveRational := {q : ℚ // 0 < q}

def valuationPairEquiv : (Nat.Primes →₀ ℤ × ℤ) ≃ PrimeValuations × PrimeValuations where
  toFun v := (v.mapRange Prod.fst rfl,v.mapRange Prod.snd rfl)
  invFun v := Finsupp.zipWith (fun i j : ℤ => (i,j)) rfl v.1 v.2
  left_inv v := by
    apply Finsupp.ext
    intro p
    rfl
  right_inv v := by
    apply Prod.ext
    · apply Finsupp.ext
      intro p
      rfl
    · apply Finsupp.ext
      intro p
      rfl

def positiveRationalPairEquiv : (Nat.Primes →₀ ℤ × ℤ) ≃ PositiveRational × PositiveRational :=
  valuationPairEquiv.trans (Equiv.prodCongr positiveRationalEquiv positiveRationalEquiv)

theorem valuationCubic_pair_eq (σ : ℝ) (v : Nat.Primes →₀ ℤ × ℤ) :
    valuationCubic σ v =
      valuationCoefficient σ (valuationPairEquiv v).1 *
      valuationCoefficient σ (valuationPairEquiv v).2 *
      valuationCoefficient σ ((valuationPairEquiv v).1+(valuationPairEquiv v).2) *
      valuationWeight σ (valuationPairEquiv v).1 * valuationWeight σ (valuationPairEquiv v).2 := by
  classical
  let u := (valuationPairEquiv v).1
  let w := (valuationPairEquiv v).2
  have hu : u.support ⊆ v.support := Finsupp.support_mapRange (hf := rfl)
  have hw : w.support ⊆ v.support := Finsupp.support_mapRange (hf := rfl)
  have huw : (u+w).support ⊆ v.support := Finsupp.support_add.trans (Finset.union_subset hu hw)
  have hcu : valuationCoefficient σ u = ∏ p ∈ v.support,coefficient (primeWeight σ p) (v p).1 :=
    u.prod_of_support_subset hu _ (fun p _ => by simp [coefficient])
  have hcw : valuationCoefficient σ w = ∏ p ∈ v.support,coefficient (primeWeight σ p) (v p).2 :=
    w.prod_of_support_subset hw _ (fun p _ => by simp [coefficient])
  have hcuw : valuationCoefficient σ (u+w) =
      ∏ p ∈ v.support,coefficient (primeWeight σ p) ((v p).1+(v p).2) :=
    (u+w).prod_of_support_subset huw _ (fun p _ => by simp [coefficient])
  have hwu : valuationWeight σ u = ∏ p ∈ v.support,primeWeight σ p^(v p).1 :=
    u.prod_of_support_subset hu _ (fun p _ => zpow_zero _)
  have hww : valuationWeight σ w = ∏ p ∈ v.support,primeWeight σ p^(v p).2 :=
    w.prod_of_support_subset hw _ (fun p _ => zpow_zero _)
  change valuationCubic σ v = valuationCoefficient σ u * valuationCoefficient σ w *
    valuationCoefficient σ (u+w)*valuationWeight σ u*valuationWeight σ w
  rw [hcu,hcw,hcuw,hwu,hww]
  simp only [valuationCubic,Finsupp.prod,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [localTriple,zpow_add₀ (primeWeight_pos σ p).ne']
  ring

def rationalCubic (σ : ℝ) (w : PositiveRational × PositiveRational) : ℝ :=
  rationalRamanujanCoefficient σ w.1 * rationalRamanujanCoefficient σ w.2 *
    rationalRamanujanCoefficient σ ⟨w.1.1*w.2.1,mul_pos w.1.2 w.2.2⟩ *
    (w.1.1 : ℝ)^(-σ) * (w.2.1 : ℝ)^(-σ)

theorem rationalCubic_eq_valuation (σ : ℝ) (a b : PositiveRational) :
    rationalCubic σ (a,b) =
      valuationCoefficient σ (positiveRationalValuations a) *
      valuationCoefficient σ (positiveRationalValuations b) *
      valuationCoefficient σ (positiveRationalValuations a+positiveRationalValuations b) *
      valuationWeight σ (positiveRationalValuations a) *
      valuationWeight σ (positiveRationalValuations b) := by
  simp only [rationalCubic,← valuationCoefficient_positiveRational,
    positiveRationalValuations_mul,valuationWeight_rational,rationalOfValuations_positive]

theorem rationalCubic_equiv (σ : ℝ) (v : Nat.Primes →₀ ℤ × ℤ) :
    rationalCubic σ (positiveRationalPairEquiv v)=valuationCubic σ v := by
  change rationalCubic σ (positiveRationalEquiv (valuationPairEquiv v).1,
    positiveRationalEquiv (valuationPairEquiv v).2)=_
  rw [rationalCubic_eq_valuation]
  simp only [positiveRationalValuations_equiv]
  exact (valuationCubic_pair_eq σ v).symm

/-- Complete signed rational-product resonance, with literal denominator coefficients. -/
theorem rationalCubic_hasSum {σ : ℝ} (hσ : 1 < σ) :
    HasSum (rationalCubic σ) ((riemannZeta (σ : ℂ)).re^2) := by
  have h := (valuationCubic_hasSum hσ).congr_fun (fun v => rationalCubic_equiv σ v)
  exact positiveRationalPairEquiv.hasSum_iff.mp h

/-- Exact absolute mass proves the unordered rational double sum is absolutely convergent. -/
theorem rationalCubic_abs_hasSum {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun w => |rationalCubic σ w|)
      ((riemannZeta (σ : ℂ)).re^2 * ∏' p, (1+4*primeWeight σ p)) := by
  have h := (valuationCubic_abs_hasSum hσ).congr_fun
    (fun v => congrArg abs (rationalCubic_equiv σ v))
  exact positiveRationalPairEquiv.hasSum_iff.mp h

def rationalOne : PositiveRational := ⟨1,zero_lt_one⟩

theorem rationalRamanujanCoefficient_one (σ : ℝ) : rationalRamanujanCoefficient σ rationalOne=1 := by
  simp [rationalRamanujanCoefficient,rationalOne,pmPowerDampedRamanujanDenominator]

theorem rationalCubic_axis_left (σ : ℝ) (a : PositiveRational) :
    rationalCubic σ (rationalOne,a)=rationalDilation σ rationalOne a := by
  simp [rationalCubic,rationalDilation,rationalRamanujanCoefficient,rationalOne,
    pmPowerDampedRamanujanDenominator]

theorem rationalCubic_axis_right (σ : ℝ) (a : PositiveRational) :
    rationalCubic σ (a,rationalOne)=rationalDilation σ rationalOne a := by
  simp [rationalCubic,rationalDilation,rationalRamanujanCoefficient,rationalOne,
    pmPowerDampedRamanujanDenominator]

private theorem rationalCubic_origin (σ : ℝ) : rationalCubic σ (rationalOne,rationalOne)=1 := by
  simp [rationalCubic,rationalRamanujanCoefficient,rationalOne,pmPowerDampedRamanujanDenominator]

private theorem mul_hasSum_rational {X Y : Type} {f : X → ℝ} {g : Y → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun v : X × Y => f v.1*g v.2) (a*b) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

private theorem remove_two_slices_hasSum {X : Type} [DecidableEq X] (e : X)
    {f : X × X → ℝ} {A B C : ℝ} (h : HasSum f A)
    (hl : HasSum (fun x => f (e,x)) B) (hr : HasSum (fun x => f (x,e)) C) :
    HasSum (fun v => if v.1=e ∨ v.2=e then 0 else f v) (A-B-C+f (e,e)) := by
  have hd := hasSum_ite_eq e (1 : ℝ)
  have hleft := mul_hasSum_rational hd hl
  have hright := mul_hasSum_rational hr hd
  have horigin := (mul_hasSum_rational hd hd).mul_left (f (e,e))
  have h' := ((h.sub hleft).sub hright).add horigin
  simp only [one_mul,mul_one] at h'
  refine h'.congr_fun ?_
  rintro ⟨x,y⟩
  by_cases hx : x=e <;> by_cases hy : y=e <;> simp [hx,hy]

def rationalOffAxesCubic (σ : ℝ) (w : PositiveRational × PositiveRational) : ℝ := by
  classical
  exact if w.1.1=1 ∨ w.2.1=1 then 0 else rationalCubic σ w

/-- Literal deletion of both arithmetic rational axes, with their intersection counted once. -/
theorem rationalOffAxesCubic_hasSum {σ : ℝ} (hσ : 1 < σ) :
    HasSum (rationalOffAxesCubic σ) (1-(riemannZeta (σ : ℂ)).re^2) := by
  classical
  have hrow : HasSum (rationalDilation σ rationalOne) ((riemannZeta (σ : ℂ)).re^2) := by
    simpa only [rationalOne,ite_true] using rationalDilation_hasSum hσ rationalOne
  have hl := hrow.congr_fun (fun a => rationalCubic_axis_left σ a)
  have hr := hrow.congr_fun (fun a => rationalCubic_axis_right σ a)
  have h := remove_two_slices_hasSum rationalOne (rationalCubic_hasSum hσ) hl hr
  rw [rationalCubic_origin] at h
  have he (x : ℝ) : x-x-x+1=1-x := by ring
  rw [he] at h
  have hcond (a : PositiveRational) : a=rationalOne ↔ a.1=1 := Subtype.ext_iff
  exact h.congr_fun (fun v => by simp only [rationalOffAxesCubic,hcond])

theorem summable_norm_rationalOffAxesCubic {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun w => ‖rationalOffAxesCubic σ w‖) := by
  apply (rationalCubic_abs_hasSum hσ).summable.of_norm_bounded
  intro w
  simp only [Real.norm_eq_abs,rationalOffAxesCubic]
  split_ifs <;> simp

end RHTower.BAGTrace
