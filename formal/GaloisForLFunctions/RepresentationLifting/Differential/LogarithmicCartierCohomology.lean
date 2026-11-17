import GaloisForLFunctions.RepresentationLifting.Differential.LogarithmicCartier

/-!
# Two-coordinate logarithmic Cartier cohomology

The two Euler operators form the logarithmic de Rham complex on finitely
supported coefficient arrays over `ZMod p`. Inverting the first nonzero
coordinate residue gives a contraction onto arrays whose two degrees are
both divisible by `p`. This identifies exact forms and classifies closed
one-forms modulo exact forms by their horizontal residues.

The construction applies the indexed splitting of Fersi, *Lifting the local
logarithmic Cartier transform modulo p^n*, §4.4, to a concrete two-coordinate
complex. Every homotopy is an explicit coefficient operator.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.LogarithmicKoszul
variable (p : ℕ) [Fact p.Prime]
abbrev Coeff := (ℕ × ℕ) →₀ ZMod p

/-- Coefficientwise multiplication preserves finite support. -/
def multiplier (a : (ℕ × ℕ) → ZMod p) : Module.End (ZMod p) (Coeff p) where
  toFun f := Finsupp.onFinset f.support (fun n => a n * f n) (fun n hn =>
    Finsupp.mem_support_iff.mpr (fun h => hn (by rw [h, mul_zero])))
  map_add' f g := by ext n; exact mul_add _ _ _
  map_smul' c f := by ext n; exact mul_left_comm _ _ _

@[simp] theorem multiplier_apply (a : (ℕ × ℕ) → ZMod p) (f : Coeff p) (n : ℕ × ℕ) :
    multiplier p a f n = a n * f n := rfl

/-- Euler differentiation in the first coordinate. -/
def dx : Module.End (ZMod p) (Coeff p) := multiplier p (fun n => n.1)
/-- Euler differentiation in the second coordinate. -/
def dy : Module.End (ZMod p) (Coeff p) := multiplier p (fun n => n.2)
/-- Inversion on nonzero first-coordinate residues. -/
def gx : Module.End (ZMod p) (Coeff p) := multiplier p (fun n => (n.1 : ZMod p)⁻¹)
/-- Second-coordinate inversion on the first-coordinate horizontal sector. -/
def gy : Module.End (ZMod p) (Coeff p) :=
  multiplier p (fun n => if (n.1 : ZMod p) = 0 then (n.2 : ZMod p)⁻¹ else 0)
/-- Projection onto simultaneous horizontal coefficients. -/
def horizontal : Module.End (ZMod p) (Coeff p) :=
  multiplier p (fun n => if (n.1 : ZMod p) = 0 ∧ (n.2 : ZMod p) = 0 then 1 else 0)

/-- Differential from functions to logarithmic one-forms. -/
def d0 (f : Coeff p) : Coeff p × Coeff p := (dx p f, dy p f)
/-- Alternating differential from one-forms to two-forms. -/
def d1 (ω : Coeff p × Coeff p) : Coeff p := dx p ω.2 - dy p ω.1
/-- Green primitive of a one-form. -/
def h1 (ω : Coeff p × Coeff p) : Coeff p := gx p ω.1 + gy p ω.2
/-- Green primitive of a two-form. -/
def h2 (f : Coeff p) : Coeff p × Coeff p := (-gy p f, gx p f)
/-- Horizontal residue of a one-form. -/
def horizontal1 (ω : Coeff p × Coeff p) : Coeff p × Coeff p :=
  (horizontal p ω.1, horizontal p ω.2)

private theorem partition (a b : ZMod p) :
    a * a⁻¹ + b * (if a = 0 then b⁻¹ else 0) =
      1 - (if a = 0 ∧ b = 0 then 1 else 0) := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

/-- Two logarithmic derivatives form a complex. -/
theorem d1_d0 (f : Coeff p) : d1 p (d0 p f) = 0 := by
  apply Finsupp.ext
  intro n
  change (n.1 : ZMod p) * (n.2 * f n) - n.2 * (n.1 * f n) = 0
  ring

/-- Green operators contract degree zero onto the simultaneous horizontal sector. -/
theorem homotopy_zero (f : Coeff p) : h1 p (d0 p f) = f - horizontal p f := by
  apply Finsupp.ext
  intro n
  change (n.1 : ZMod p)⁻¹ * (n.1 * f n) +
    (if (n.1 : ZMod p) = 0 then (n.2 : ZMod p)⁻¹ else 0) * (n.2 * f n) =
      f n - (if (n.1 : ZMod p) = 0 ∧ (n.2 : ZMod p) = 0 then 1 else 0) * f n
  have h := partition p (n.1 : ZMod p) (n.2 : ZMod p)
  linear_combination (f n) * h

/-- The middle-degree contraction gives an explicit logarithmic Poincaré lemma. -/
theorem homotopy_one (ω : Coeff p × Coeff p) :
    d0 p (h1 p ω) + h2 p (d1 p ω) = ω - horizontal1 p ω := by
  apply Prod.ext
  · apply Finsupp.ext
    intro n
    change (n.1 : ZMod p) * ((n.1 : ZMod p)⁻¹ * ω.1 n +
      (if (n.1 : ZMod p) = 0 then (n.2 : ZMod p)⁻¹ else 0) * ω.2 n) +
      -((if (n.1 : ZMod p) = 0 then (n.2 : ZMod p)⁻¹ else 0) *
        ((n.1 : ZMod p) * ω.2 n - (n.2 : ZMod p) * ω.1 n)) =
      ω.1 n - (if (n.1 : ZMod p) = 0 ∧ (n.2 : ZMod p) = 0 then 1 else 0) * ω.1 n
    have h := partition p (n.1 : ZMod p) (n.2 : ZMod p)
    linear_combination (ω.1 n) * h
  · apply Finsupp.ext
    intro n
    change (n.2 : ZMod p) * ((n.1 : ZMod p)⁻¹ * ω.1 n +
      (if (n.1 : ZMod p) = 0 then (n.2 : ZMod p)⁻¹ else 0) * ω.2 n) +
      (n.1 : ZMod p)⁻¹ * ((n.1 : ZMod p) * ω.2 n - (n.2 : ZMod p) * ω.1 n) =
      ω.2 n - (if (n.1 : ZMod p) = 0 ∧ (n.2 : ZMod p) = 0 then 1 else 0) * ω.2 n
    have h := partition p (n.1 : ZMod p) (n.2 : ZMod p)
    linear_combination (ω.2 n) * h

/-- Top-degree forms have exactly their simultaneous horizontal obstruction. -/
theorem homotopy_two (f : Coeff p) : d1 p (h2 p f) = f - horizontal p f := by
  apply Finsupp.ext
  intro n
  change (n.1 : ZMod p) * ((n.1 : ZMod p)⁻¹ * f n) -
    (n.2 : ZMod p) * (-((if (n.1 : ZMod p) = 0 then (n.2 : ZMod p)⁻¹ else 0) * f n)) =
    f n - (if (n.1 : ZMod p) = 0 ∧ (n.2 : ZMod p) = 0 then 1 else 0) * f n
  have h := partition p (n.1 : ZMod p) (n.2 : ZMod p)
  linear_combination (f n) * h

@[simp] theorem horizontal_dx (f : Coeff p) : horizontal p (dx p f) = 0 := by
  apply Finsupp.ext
  intro n
  change (if (n.1 : ZMod p) = 0 ∧ (n.2 : ZMod p) = 0 then 1 else 0) *
    ((n.1 : ZMod p) * f n) = 0
  split_ifs with h
  · simp only [h.1, zero_mul, mul_zero]
  · exact zero_mul _

@[simp] theorem horizontal_dy (f : Coeff p) : horizontal p (dy p f) = 0 := by
  apply Finsupp.ext
  intro n
  change (if (n.1 : ZMod p) = 0 ∧ (n.2 : ZMod p) = 0 then 1 else 0) *
    ((n.2 : ZMod p) * f n) = 0
  split_ifs with h
  · simp only [h.2, zero_mul, mul_zero]
  · exact zero_mul _

@[simp] theorem horizontal1_d0 (f : Coeff p) : horizontal1 p (d0 p f) = 0 := by
  change (horizontal p (dx p f), horizontal p (dy p f)) = 0
  rw [horizontal_dx, horizontal_dy]
  rfl

@[simp] theorem horizontal_d1 (ω : Coeff p × Coeff p) : horizontal p (d1 p ω) = 0 := by
  rw [d1, map_sub, horizontal_dx, horizontal_dy, sub_self]

@[simp] theorem d0_horizontal (f : Coeff p) : d0 p (horizontal p f) = 0 := by
  apply Prod.ext
  · apply Finsupp.ext
    intro n
    change (n.1 : ZMod p) *
      ((if (n.1 : ZMod p) = 0 ∧ (n.2 : ZMod p) = 0 then 1 else 0) * f n) = 0
    split_ifs with h
    · rw [h.1, zero_mul]
    · rw [zero_mul, mul_zero]
  · apply Finsupp.ext
    intro n
    change (n.2 : ZMod p) *
      ((if (n.1 : ZMod p) = 0 ∧ (n.2 : ZMod p) = 0 then 1 else 0) * f n) = 0
    split_ifs with h
    · rw [h.2, zero_mul]
    · rw [zero_mul, mul_zero]

/-- Horizontal functions are precisely the simultaneous zero-residue coefficients. -/
theorem kernel_d0 (f : Coeff p) : d0 p f = 0 ↔ horizontal p f = f := by
  constructor
  · intro h
    have hc := homotopy_zero p f
    rw [h] at hc
    have hz : h1 p 0 = 0 := by simp [h1]
    rw [hz] at hc
    exact (sub_eq_zero.mp hc.symm).symm
  · intro h
    rw [← h, d0_horizontal]

/-- A closed logarithmic one-form is exact precisely when both horizontal residues vanish. -/
theorem exact_one_iff (ω : Coeff p × Coeff p) :
    (∃ f, d0 p f = ω) ↔ d1 p ω = 0 ∧ horizontal1 p ω = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨d1_d0 p f, horizontal1_d0 p f⟩
  · rintro ⟨hc, hr⟩
    refine ⟨h1 p ω, ?_⟩
    have h := homotopy_one p ω
    rw [hc, hr, sub_zero] at h
    have hz : h2 p 0 = 0 := by simp [h2]
    simpa only [hz, add_zero] using h

/-- A top-degree logarithmic form is exact precisely when its horizontal residue vanishes. -/
theorem exact_two_iff (f : Coeff p) :
    (∃ ω, d1 p ω = f) ↔ horizontal p f = 0 := by
  constructor
  · rintro ⟨ω, rfl⟩
    exact horizontal_d1 p ω
  · intro h
    exact ⟨h2 p f, by simpa only [h, sub_zero] using homotopy_two p f⟩

/-- Closed forms have the same cohomology class exactly when their residues agree. -/
theorem cohomologous_one_iff (ω η : Coeff p × Coeff p)
    (hω : d1 p ω = 0) (hη : d1 p η = 0) :
    (∃ f, d0 p f = ω - η) ↔ horizontal1 p ω = horizontal1 p η := by
  have hd : d1 p (ω - η) = 0 := by
    have he : d1 p (ω - η) = d1 p ω - d1 p η := by
      simp only [d1, Prod.fst_sub, Prod.snd_sub, map_sub]
      abel
    rw [he, hω, hη, sub_self]
  have hr : horizontal1 p (ω - η) = horizontal1 p ω - horizontal1 p η := by
    simp only [horizontal1, Prod.fst_sub, Prod.snd_sub, map_sub]
    rfl
  simp only [exact_one_iff, hd, hr, sub_eq_zero, true_and]

#print axioms kernel_d0
#print axioms exact_one_iff
#print axioms exact_two_iff
#print axioms cohomologous_one_iff
#print axioms homotopy_zero
#print axioms homotopy_one
#print axioms homotopy_two
end GaloisForLFunctions.RepresentationLifting.LogarithmicKoszul
