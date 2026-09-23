import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import GaloisForLFunctions.HTGeometry.WeightedGraphSpectralGap

/-!
# The design identity and the spectral bound of an incidence structure

Garland's method needs a spectral gap for the links of the Bruhat--Tits building, and those links
are spherical buildings over the residue field.  The governing rank-two case is the point--line
incidence structure of a projective plane, whose spectral behaviour is forced by one algebraic
identity: two distinct points lie on exactly one line, and each point lies on `q + 1` lines.

* `sum_incidence_sq` : **the design identity** — the squared length of a transported function.
* `sum_incidence_sq_of_sum_eq_zero`, `sum_incidence_sq_projectivePlane` : on functions of sum zero
  the transport multiplies the squared length by `r - lam`, which is `q` for a projective plane.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

section Design

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P]

/-- **The design identity.**  If any two distinct points lie on exactly `lam` common lines and each
point lies on `r` lines, then the squared length of the transported function is
`(r - lam)` times its squared length plus `lam` times the square of its sum. -/
theorem sum_incidence_sq (N : P → L → ℝ) (r lam : ℝ)
    (hdesign : ∀ p p' : P, (∑ l, N p l * N p' l) = if p = p' then r else lam)
    (f : P → ℝ) :
    (∑ l, (∑ p, N p l * f p) ^ (2 : ℕ))
      = (r - lam) * (∑ p, (f p) ^ (2 : ℕ)) + lam * (∑ p, f p) ^ (2 : ℕ) := by
  classical
  have hexpand : ∀ l : L, (∑ p, N p l * f p) ^ (2 : ℕ)
      = ∑ p, ∑ p', (N p l * f p) * (N p' l * f p') := by
    intro l
    rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun l (_ : l ∈ univ) => hexpand l), Finset.sum_comm]
  have hswap : ∀ p : P, ∑ l, ∑ p', (N p l * f p) * (N p' l * f p')
      = ∑ p', (f p * f p') * (∑ l, N p l * N p' l) := by
    intro p
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ univ) => hswap p)]
  have hval : ∀ p p' : P, (f p * f p') * (∑ l, N p l * N p' l)
      = lam * (f p * f p') + (if p = p' then (r - lam) * (f p * f p') else 0) := by
    intro p p'
    rw [hdesign p p']
    by_cases h : p = p'
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ univ) =>
    Finset.sum_congr rfl (fun p' (_ : p' ∈ univ) => hval p p'))]
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ univ) => Finset.sum_add_distrib)]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ p : P, ∑ p' : P, lam * (f p * f p') = lam * (∑ p, f p) ^ (2 : ℕ) := by
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
  have h2 : ∑ p : P, ∑ p' : P, (if p = p' then (r - lam) * (f p * f p') else 0)
      = (r - lam) * ∑ p, (f p) ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_ite_eq _ p (fun p' => (r - lam) * (f p * f p')), if_pos (Finset.mem_univ p),
      pow_two]
  rw [h1, h2]
  ring

/-- **The design identity on functions of sum zero.**  For a `2`-design the transported function
has squared length exactly `r - lam` times the original. -/
theorem sum_incidence_sq_of_sum_eq_zero (N : P → L → ℝ) (r lam : ℝ)
    (hdesign : ∀ p p' : P, (∑ l, N p l * N p' l) = if p = p' then r else lam)
    (f : P → ℝ) (hf : (∑ p, f p) = 0) :
    (∑ l, (∑ p, N p l * f p) ^ (2 : ℕ)) = (r - lam) * (∑ p, (f p) ^ (2 : ℕ)) := by
  rw [sum_incidence_sq N r lam hdesign f, hf]
  ring

/-- **The projective-plane case.**  Two distinct points lie on exactly one line and each point lies
on `q + 1` lines, so a function of sum zero is transported with squared length multiplied by `q`. -/
theorem sum_incidence_sq_projectivePlane (N : P → L → ℝ) (q : ℝ)
    (hdesign : ∀ p p' : P, (∑ l, N p l * N p' l) = if p = p' then q + 1 else 1)
    (f : P → ℝ) (hf : (∑ p, f p) = 0) :
    (∑ l, (∑ p, N p l * f p) ^ (2 : ℕ)) = q * (∑ p, (f p) ^ (2 : ℕ)) := by
  rw [sum_incidence_sq_of_sum_eq_zero N (q + 1) 1 hdesign f hf]
  ring


/-- **The incidence pairing bound.**  For a `2`-design and a function of sum zero on the points, the
pairing against any function on the lines is bounded by `√(r - lam)` times the sum of the two
squared lengths.  This is Cauchy--Schwarz against the design identity, followed by the arithmetic
mean bound. -/
theorem two_mul_incidence_le (N : P → L → ℝ) (r lam : ℝ) (hrl : 0 ≤ r - lam)
    (hdesign : ∀ p p' : P, (∑ l, N p l * N p' l) = if p = p' then r else lam)
    (a : P → ℝ) (b : L → ℝ) (ha : (∑ p, a p) = 0) :
    2 * (∑ p, ∑ l, N p l * (a p * b l))
      ≤ Real.sqrt (r - lam) * ((∑ p, (a p) ^ (2 : ℕ)) + (∑ l, (b l) ^ (2 : ℕ))) := by
  classical
  have hT : (∑ p, ∑ l, N p l * (a p * b l)) = ∑ l, (∑ p, N p l * a p) * b l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset L) (fun l => ∑ p, N p l * a p) b
  rw [sum_incidence_sq_of_sum_eq_zero N r lam hdesign a ha] at hCS
  set A : ℝ := ∑ p, (a p) ^ (2 : ℕ) with hAdef
  set B : ℝ := ∑ l, (b l) ^ (2 : ℕ) with hBdef
  set T : ℝ := ∑ l, (∑ p, N p l * a p) * b l with hTdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hAB : 0 ≤ A + B := by linarith
  have h4 : (2 * T) ^ (2 : ℕ) ≤ (r - lam) * (A + B) ^ (2 : ℕ) := by
    nlinarith [hCS, mul_nonneg hrl (sq_nonneg (A - B))]
  have hfin : 2 * T ≤ Real.sqrt ((r - lam) * (A + B) ^ (2 : ℕ)) :=
    calc 2 * T ≤ |2 * T| := le_abs_self _
      _ = Real.sqrt ((2 * T) ^ (2 : ℕ)) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((r - lam) * (A + B) ^ (2 : ℕ)) := Real.sqrt_le_sqrt h4
  rw [Real.sqrt_mul hrl, Real.sqrt_sq hAB] at hfin
  rw [hT]
  exact hfin


/-! ## The incidence graph -/

/-- The weight of the bipartite incidence graph. -/
def incW (N : P → L → ℝ) : (P ⊕ L) → (P ⊕ L) → ℝ
  | Sum.inl p, Sum.inr l => N p l
  | Sum.inr l, Sum.inl p => N p l
  | _, _ => 0

/-- **The bipartite incidence graph of an incidence structure.** -/
def incidenceGraph (N : P → L → ℝ) (hN : ∀ p l, 0 ≤ N p l) : WeightedGraph (P ⊕ L) where
  w := incW N
  w_symm u v := by cases u <;> cases v <;> rfl
  w_nonneg u v := by
    cases u <;> cases v
    · exact le_rfl
    · exact hN _ _
    · exact hN _ _
    · exact le_rfl
  w_diag v := by cases v <;> rfl

omit [DecidableEq P] in
theorem incidenceGraph_mass_inl (N : P → L → ℝ) (hN : ∀ p l, 0 ≤ N p l) (p : P) :
    (incidenceGraph N hN).mass (Sum.inl p) = ∑ l, N p l := by
  show ∑ y : P ⊕ L, incW N (Sum.inl p) y = _
  rw [Fintype.sum_sum_type]
  have h1 : ∑ p' : P, incW N (Sum.inl p) (Sum.inl p') = 0 := Finset.sum_eq_zero fun _ _ => rfl
  rw [h1, zero_add]
  rfl

omit [DecidableEq P] in
theorem incidenceGraph_mass_inr (N : P → L → ℝ) (hN : ∀ p l, 0 ≤ N p l) (l : L) :
    (incidenceGraph N hN).mass (Sum.inr l) = ∑ p, N p l := by
  show ∑ y : P ⊕ L, incW N (Sum.inr l) y = _
  rw [Fintype.sum_sum_type]
  have h2 : ∑ l' : L, incW N (Sum.inr l) (Sum.inr l') = 0 := Finset.sum_eq_zero fun _ _ => rfl
  rw [h2, add_zero]
  rfl

omit [DecidableEq P] in
/-- **The averaging form of the incidence graph.** -/
theorem incidenceGraph_averaging (N : P → L → ℝ) (hN : ∀ p l, 0 ≤ N p l) (f : P ⊕ L → ℝ) :
    (∑ x : P ⊕ L, ∑ y : P ⊕ L, (incidenceGraph N hN).w x y * (f x * f y))
      = 2 * ∑ p, ∑ l, N p l * (f (Sum.inl p) * f (Sum.inr l)) := by
  rw [Fintype.sum_sum_type]
  have hP : ∀ p : P, (∑ y : P ⊕ L, (incidenceGraph N hN).w (Sum.inl p) y
        * (f (Sum.inl p) * f y))
      = ∑ l, N p l * (f (Sum.inl p) * f (Sum.inr l)) := by
    intro p
    rw [Fintype.sum_sum_type]
    have h1 : ∑ p' : P, (incidenceGraph N hN).w (Sum.inl p) (Sum.inl p')
        * (f (Sum.inl p) * f (Sum.inl p')) = 0 :=
      Finset.sum_eq_zero fun p' _ => by
        show (0:ℝ) * (f (Sum.inl p) * f (Sum.inl p')) = 0
        rw [zero_mul]
    rw [h1, zero_add]
    rfl
  have hL : ∀ l : L, (∑ y : P ⊕ L, (incidenceGraph N hN).w (Sum.inr l) y
        * (f (Sum.inr l) * f y))
      = ∑ p, N p l * (f (Sum.inl p) * f (Sum.inr l)) := by
    intro l
    rw [Fintype.sum_sum_type]
    have h2 : ∑ l' : L, (incidenceGraph N hN).w (Sum.inr l) (Sum.inr l')
        * (f (Sum.inr l) * f (Sum.inr l')) = 0 :=
      Finset.sum_eq_zero fun l' _ => by
        show (0:ℝ) * (f (Sum.inr l) * f (Sum.inr l')) = 0
        rw [zero_mul]
    rw [h2, add_zero]
    exact Finset.sum_congr rfl fun p _ => by
      show N p l * (f (Sum.inr l) * f (Sum.inl p)) = _
      ring
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ univ) => hP p),
    Finset.sum_congr rfl (fun l (_ : l ∈ univ) => hL l), Finset.sum_comm]
  ring


omit [DecidableEq P] in
theorem incidenceGraph_massInner (N : P → L → ℝ) (hN : ∀ p l, 0 ≤ N p l) (r : ℝ)
    (hdegP : ∀ p, (∑ l, N p l) = r) (hdegL : ∀ l, (∑ p, N p l) = r) (f : P ⊕ L → ℝ) :
    (incidenceGraph N hN).massInner f f
      = r * ((∑ p, f (Sum.inl p) ^ (2 : ℕ)) + ∑ l, f (Sum.inr l) ^ (2 : ℕ)) := by
  rw [WeightedGraph.massInner, Fintype.sum_sum_type]
  have h1 : ∀ p : P, (incidenceGraph N hN).mass (Sum.inl p) * (f (Sum.inl p) * f (Sum.inl p))
      = r * f (Sum.inl p) ^ (2 : ℕ) := fun p => by
    rw [incidenceGraph_mass_inl, hdegP p, pow_two]
  have h2 : ∀ l : L, (incidenceGraph N hN).mass (Sum.inr l) * (f (Sum.inr l) * f (Sum.inr l))
      = r * f (Sum.inr l) ^ (2 : ℕ) := fun l => by
    rw [incidenceGraph_mass_inr, hdegL l, pow_two]
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ univ) => h1 p),
    Finset.sum_congr rfl (fun l (_ : l ∈ univ) => h2 l), ← Finset.mul_sum, ← Finset.mul_sum]
  ring

omit [DecidableEq P] in
theorem incidenceGraph_sum_eq_zero (N : P → L → ℝ) (hN : ∀ p l, 0 ≤ N p l) (r : ℝ) (hr : r ≠ 0)
    (hdegP : ∀ p, (∑ l, N p l) = r) (hdegL : ∀ l, (∑ p, N p l) = r) (f : P ⊕ L → ℝ)
    (hf : (∑ x, (incidenceGraph N hN).mass x * f x) = 0) :
    (∑ p, f (Sum.inl p)) + (∑ l, f (Sum.inr l)) = 0 := by
  rw [Fintype.sum_sum_type] at hf
  have h1 : ∀ p : P, (incidenceGraph N hN).mass (Sum.inl p) * f (Sum.inl p)
      = r * f (Sum.inl p) := fun p => by rw [incidenceGraph_mass_inl, hdegP p]
  have h2 : ∀ l : L, (incidenceGraph N hN).mass (Sum.inr l) * f (Sum.inr l)
      = r * f (Sum.inr l) := fun l => by rw [incidenceGraph_mass_inr, hdegL l]
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ univ) => h1 p),
    Finset.sum_congr rfl (fun l (_ : l ∈ univ) => h2 l), ← Finset.mul_sum, ← Finset.mul_sum,
    ← mul_add] at hf
  exact (mul_eq_zero.1 hf).resolve_left hr


omit [DecidableEq P] in
/-- **The pairing after shifting both functions by constants.** -/
theorem incidence_pairing_shift (N : P → L → ℝ) (r : ℝ)
    (hdegP : ∀ p, (∑ l, N p l) = r) (hdegL : ∀ l, (∑ p, N p l) = r)
    (a : P → ℝ) (b : L → ℝ) (al be : ℝ)
    (ha0 : (∑ p, (a p - al)) = 0) (hb0 : (∑ l, (b l - be)) = 0) :
    (∑ p, ∑ l, N p l * (a p * b l))
      = (∑ p, ∑ l, N p l * ((a p - al) * (b l - be)))
        + al * be * ((Fintype.card P : ℝ) * r) := by
  have e1 : (∑ p, ∑ l, N p l * (a p - al)) = 0 := by
    have h : ∀ p : P, (∑ l, N p l * (a p - al)) = r * (a p - al) := fun p => by
      rw [← Finset.sum_mul, hdegP p]
    rw [Finset.sum_congr rfl (fun p (_ : p ∈ univ) => h p), ← Finset.mul_sum, ha0, mul_zero]
  have e2 : (∑ p, ∑ l, N p l * (b l - be)) = 0 := by
    rw [Finset.sum_comm]
    have h : ∀ l : L, (∑ p, N p l * (b l - be)) = r * (b l - be) := fun l => by
      rw [← Finset.sum_mul, hdegL l]
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ univ) => h l), ← Finset.mul_sum, hb0, mul_zero]
  have e3 : (∑ p : P, ∑ l, N p l) = (Fintype.card P : ℝ) * r := by
    rw [Finset.sum_congr rfl (fun p (_ : p ∈ univ) => hdegP p), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have key : ∀ (p : P) (l : L), N p l * (a p * b l)
      = N p l * ((a p - al) * (b l - be)) + be * (N p l * (a p - al))
        + al * (N p l * (b l - be)) + al * be * N p l := fun p l => by ring
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ univ) =>
    Finset.sum_congr rfl (fun l (_ : l ∈ univ) => key p l))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e1, e2, e3]
  ring


theorem sum_sq_sub_const {ι : Type*} [Fintype ι] (g : ι → ℝ) (c : ℝ)
    (hc : (∑ i, g i) = c * (Fintype.card ι : ℝ)) :
    (∑ i, (g i) ^ (2 : ℕ)) = (∑ i, (g i - c) ^ (2 : ℕ)) + c ^ (2 : ℕ) * (Fintype.card ι : ℝ) := by
  have hexp : ∀ i : ι, (g i - c) ^ (2 : ℕ) = (g i) ^ (2 : ℕ) - 2 * c * (g i) + c ^ (2 : ℕ) := fun i => by ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ univ) => hexp i), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  ring


/-- **The spectral gap of the incidence graph of a symmetric `2`-design.**  The design identity
bounds the pairing of the two mean-zero parts, and the constant parts cancel in the right direction:
they lower the averaging form and raise the mass norm. -/
theorem incidenceGraph_hasSpectralGap [Nonempty P] (N : P → L → ℝ)
    (hN : ∀ p l, 0 ≤ N p l) (r lam : ℝ) (hr : 0 < r) (hrl : 0 ≤ r - lam)
    (hcard : Fintype.card P = Fintype.card L)
    (hdegP : ∀ p, (∑ l, N p l) = r) (hdegL : ∀ l, (∑ p, N p l) = r)
    (hdesign : ∀ p p' : P, (∑ l, N p l * N p' l) = if p = p' then r else lam) :
    (incidenceGraph N hN).HasSpectralGap (1 - Real.sqrt (r - lam) / r) := by
  classical
  refine (incidenceGraph N hN).hasSpectralGap_of_bound (Real.sqrt (r - lam) / r) ?_
  intro f hf
  have hvpos : (0 : ℝ) < (Fintype.card P : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcardL : (Fintype.card L : ℝ) = (Fintype.card P : ℝ) := by rw [hcard]
  obtain ⟨al, hal⟩ : ∃ c : ℝ, (∑ p, f (Sum.inl p)) = c * (Fintype.card P : ℝ) :=
    ⟨(∑ p, f (Sum.inl p)) / (Fintype.card P : ℝ), by field_simp⟩
  obtain ⟨be, hbe⟩ : ∃ c : ℝ, (∑ l, f (Sum.inr l)) = c * (Fintype.card P : ℝ) :=
    ⟨(∑ l, f (Sum.inr l)) / (Fintype.card P : ℝ), by field_simp⟩
  have hzero := incidenceGraph_sum_eq_zero N hN r hr.ne' hdegP hdegL f hf
  have hab : be = -al := by
    rw [hal, hbe] at hzero
    have hz : (al + be) * (Fintype.card P : ℝ) = 0 := by linarith
    have h0 := (mul_eq_zero.1 hz).resolve_right hvpos.ne'
    linarith
  subst hab
  have ha0 : (∑ p, (f (Sum.inl p) - al)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hal]
    ring
  have hb0 : (∑ l, (f (Sum.inr l) - -al)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardL, hbe]
    ring
  have hA := sum_sq_sub_const (fun p => f (Sum.inl p)) al hal
  have hB := sum_sq_sub_const (fun l => f (Sum.inr l)) (-al) (by rw [hcardL]; exact hbe)
  have hCS := two_mul_incidence_le N r lam hrl hdesign
    (fun p => f (Sum.inl p) - al) (fun l => f (Sum.inr l) - -al) ha0
  have hshift := incidence_pairing_shift N r hdegP hdegL
    (fun p => f (Sum.inl p)) (fun l => f (Sum.inr l)) al (-al) ha0 hb0
  rw [incidenceGraph_averaging N hN f, hshift, incidenceGraph_massInner N hN r hdegP hdegL f,
    hA, hB, hcardL]
  have hdiv : ∀ X : ℝ, Real.sqrt (r - lam) / r * (r * X) = Real.sqrt (r - lam) * X := fun X => by
    field_simp
  rw [hdiv]
  have hsq : (0:ℝ) ≤ Real.sqrt (r - lam) := Real.sqrt_nonneg _
  have hcorner : (0:ℝ) ≤ al ^ (2 : ℕ) * (Fintype.card P : ℝ) := mul_nonneg (sq_nonneg _) hvpos.le
  nlinarith [hCS, mul_nonneg hsq hcorner, mul_nonneg hcorner hr.le]


end Design

end GaloisForLFunctions.HTGeometry
