import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringSubsetExpansion

/-!
# Exponential tau solutions of the five simple cubic Hirota equations

Evaluate the bilinear operator by differentiating the two-copy product
at opposite shifts. The mixed derivatives of each exponential give the
two frequency differences. Grouping its two occupied wave sets proves
the equation for every finite list of positive momenta.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy.WaveList
variable {α : Type*}

private def ksum (k : α → ℝ) (a : List α) := (a.map k).sum
private def tsum (k : α → ℝ) (a : List α) := cubicSum (a.map k)

private def shifted (k A : α → ℝ) (x t : ℝ) (z : α) := A z*Real.exp (k z*x+(k z)^3*t)

/-- Tau is the occupied-set expansion with exponential spatial and temporal phases. -/
def tau (k A : α → ℝ) (xs : List α) (x t : ℝ) :=
  subsetSum xs (amplitude k (shifted k A x t))

private theorem shifted_amplitude (k A : α → ℝ) (x t h u : ℝ) (a : List α) :
    amplitude k (shifted k A (x+h) (t+u)) a =
      amplitude k (shifted k A x t) a*Real.exp (ksum k a*h+tsum k a*u) := by
  have eq : product (shifted k A (x+h) (t+u)) a =
      product (shifted k A x t) a*Real.exp (ksum k a*h+tsum k a*u) := by
    induction a with
    | nil => simp [product,ksum,tsum,cubicSum]
    | cons z a ih =>
      change shifted k A (x+h) (t+u) z*product (shifted k A (x+h) (t+u)) a = _
      rw [ih]
      change _=(shifted k A x t z*product (shifted k A x t) a)*
        Real.exp ((k z+ksum k a)*h+((k z)^3+tsum k a)*u)
      unfold shifted
      rw [show k z*(x+h)+(k z)^3*(t+u)=(k z*x+(k z)^3*t)+(k z*h+(k z)^3*u) by ring,
        show (k z+ksum k a)*h+((k z)^3+tsum k a)*u =
          (k z*h+(k z)^3*u)+(ksum k a*h+tsum k a*u) by ring,
        Real.exp_add (k z*x+(k z)^3*t) (k z*h+(k z)^3*u),
        Real.exp_add (k z*h+(k z)^3*u) (ksum k a*h+tsum k a*u)]
      ring
  simp only [amplitude,eq,mul_assoc]

private theorem subset_scale (xs : List α) (c : ℝ) (F : List α → ℝ) :
    subsetSum xs (fun a => c*F a)=c*subsetSum xs F := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih => simp only [subsetSum,ih,mul_add]

private theorem subset_mul (xs : List α) (F G : List α → ℝ) :
    subsetSum xs F*subsetSum xs G=paired xs (fun a b => F a*G b) := by
  simp only [paired,subset_scale]
  rw [mul_comm,← subset_scale]
  congr 1
  funext a
  exact mul_comm _ _

private theorem subset_deriv (xs : List α) (F : List α → ℝ → ℝ) (G : List α → ℝ) (z : ℝ)
    (hd : ∀ a, HasDerivAt (F a) (G a) z) :
    HasDerivAt (fun h => subsetSum xs fun a => F a h) (subsetSum xs G) z := by
  induction xs generalizing F G with
  | nil => exact hd []
  | cons x xs ih => exact (ih F G hd).add (ih _ _ fun a => hd (x::a))

private theorem paired_deriv (xs : List α) (F : List α → List α → ℝ → ℝ)
    (G : List α → List α → ℝ) (z : ℝ) (hd : ∀ a b, HasDerivAt (F a b) (G a b) z) :
    HasDerivAt (fun h => paired xs fun a b => F a b h) (paired xs G) z :=
  subset_deriv xs _ _ _ fun a => subset_deriv xs _ _ _ (hd a)

private abbrev Coeff (α : Type*) := List α → List α → ℝ

private def modeSum (xs : List α) (B U V : Coeff α) (p q : ℕ) (h u : ℝ) :=
  paired xs fun a b => B a b*(U a b)^p*(V a b)^q*Real.exp (U a b*h+V a b*u)

private theorem dx (xs : List α) (B U V : Coeff α) (p q : ℕ) (h u : ℝ) :
    deriv (fun s => modeSum xs B U V p q s u) h=modeSum xs B U V (p+1) q h u := by
  apply HasDerivAt.deriv
  apply paired_deriv
  intro a b
  have he := (((hasDerivAt_id h).const_mul (U a b)).add_const (V a b*u)).exp
  rw [show B a b*(U a b)^(p+1)*(V a b)^q*Real.exp (U a b*h+V a b*u) =
    (B a b*(U a b)^p*(V a b)^q)*(Real.exp (U a b*h+V a b*u)*(U a b*1)) by rw [pow_succ]; ring]
  exact he.const_mul _

private theorem dt (xs : List α) (B U V : Coeff α) (p q : ℕ) (h u : ℝ) :
    deriv (modeSum xs B U V p q h) u=modeSum xs B U V p (q+1) h u := by
  apply HasDerivAt.deriv
  apply paired_deriv
  intro a b
  have he := (((hasDerivAt_id u).const_mul (V a b)).const_add (U a b*h)).exp
  rw [show B a b*(U a b)^p*(V a b)^(q+1)*Real.exp (U a b*h+V a b*u) =
    (B a b*(U a b)^p*(V a b)^q)*(Real.exp (U a b*h+V a b*u)*(V a b*1)) by rw [pow_succ]; ring]
  exact he.const_mul _

/-- Differentiate p times in space and q times in time in the shift variables. -/
def jet (f : ℝ → ℝ → ℝ) (p q : ℕ) :=
  (deriv^[p] (fun h => (deriv^[q] (f h)) 0)) 0

private theorem jet_modes (xs : List α) (B U V : Coeff α) (p q : ℕ) :
    jet (modeSum xs B U V 0 0) p q=paired xs fun a b => B a b*(U a b)^p*(V a b)^q := by
  have time (h : ℝ) (j : ℕ) : deriv^[j] (modeSum xs B U V 0 0 h)=modeSum xs B U V 0 j h := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply',ih]; exact funext (dt _ _ _ _ _ _ _)
  have space (i : ℕ) : deriv^[i] (fun h => modeSum xs B U V 0 q h 0) =
      fun h => modeSum xs B U V i q h 0 := by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply',ih]; exact funext fun h => dx _ _ _ _ _ _ h _
  unfold jet
  simp only [time]
  rw [space p]
  simp only [modeSum,mul_zero,add_zero,Real.exp_zero,mul_one]

private def weights (w : Weights) : List (ℕ × ℕ × ℝ) :=
  [(4,0,w.w4),(1,1,-w.w4),
   (6,0,w.w6),(3,1,w.w6),(0,2,-2*w.w6),
   (8,0,w.w8),(5,1,-5*w.w8),(2,2,4*w.w8),
   (10,0,w.w10),(7,1,-3*w.w10),(4,2,-6*w.w10),(1,3,8*w.w10),
   (12,0,w.w12),(9,1,23*w.w12),(6,2,-120*w.w12),(3,3,32*w.w12),(0,4,64*w.w12)]

private def applyWeights : List (ℕ × ℕ × ℝ) → (ℕ → ℕ → ℝ) → ℝ
  | [],_ => 0
  | (p,q,c)::xs,J => c * J p q+applyWeights xs J

private theorem weights_symbol (w : Weights) (s t : ℝ) :
    applyWeights (weights w) (fun p q => s^p*t^q)=dispersion w s t := by
  simp only [weights,applyWeights,dispersion,graph]
  ring

private theorem weighted_modes (xs : List α) (B U V : Coeff α) (ds : List (ℕ × ℕ × ℝ)) :
    applyWeights ds (jet (modeSum xs B U V 0 0)) =
    paired xs (fun a b => B a b*applyWeights ds (fun p q => (U a b)^p*(V a b)^q)) := by
  have zero : subsetSum xs (fun _ => 0)=0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [subsetSum,ih,add_zero]
  induction ds with
  | nil => simp only [applyWeights,mul_zero,paired,zero]
  | cons d ds ih =>
    obtain ⟨p,q,c⟩ := d
    rw [applyWeights,jet_modes,ih]
    have linear (a b : List α) :
        B a b*(c*((U a b)^p*(V a b)^q)+applyWeights ds (fun i j => (U a b)^i*(V a b)^j)) =
        c*(B a b*(U a b)^p*(V a b)^q)+B a b*applyWeights ds (fun i j => (U a b)^i*(V a b)^j) := by ring
    simp only [paired,applyWeights,linear,subset_add,subset_scale]

/-- The bilinear differential residual at an actual point of a scalar field. -/
def hirota (w : Weights) (f : ℝ → ℝ → ℝ) (x t : ℝ) :=
  applyWeights (weights w) (jet fun h u => f (x+h) (t+u)*f (x-h) (t-u))

/-- Every finite superposition with the Cauchy pair phases solves all five
simple cubic flows simultaneously, with actual iterated derivatives. -/
theorem tau_solves_hirota (w : Weights) (k : α → {z : ℝ // 0<z}) (A : α → ℝ) (xs : List α) (x t : ℝ) :
    hirota w (tau (fun z => (k z).val) A xs) x t=0 := by
  let K := fun z => (k z).val
  let W := shifted K A x t
  let B := fun a b => amplitude K W a*amplitude K W b
  let U := fun a b => ksum K a-ksum K b
  let V := fun a b => tsum K a-tsum K b
  have he : (fun h u => tau K A xs (x+h) (t+u)*tau K A xs (x-h) (t-u)) =
      modeSum xs B U V 0 0 := by
    funext h u
    rw [tau,tau,subset_mul]
    apply congrArg (paired xs)
    funext a b
    rw [shifted_amplitude,sub_eq_add_neg,sub_eq_add_neg,shifted_amplitude]
    simp only [B,U,V,W,pow_zero,mul_one]
    rw [← show (ksum K a*h+tsum K a*u)+(ksum K b*(-h)+tsum K b*(-u)) =
      (ksum K a-ksum K b)*h+(tsum K a-tsum K b)*u by ring,
      Real.exp_add (ksum K a*h+tsum K a*u) (ksum K b*(-h)+tsum K b*(-u))]
    ring
  change applyWeights (weights w) (jet _) = 0
  rw [he,weighted_modes]
  simp only [weights_symbol]
  exact full_symbol_cancellation w k W xs

#print axioms tau_solves_hirota
end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy.WaveList
