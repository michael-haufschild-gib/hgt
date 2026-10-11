import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Lee–Yang theorem for ferromagnetic graphs, by Asano contraction

For a finite site set `V`, bonds `E ⊆ V × V` between distinct sites and real couplings
`|a_{ij}| ≤ 1`, the Ising polynomial is

`Z(z) = Σ_{S ⊆ V} ∏_{k∈S} z_k ∏_{(i,j)∈E} a_{ij}^{[(i,j) crosses S]}`.

With `a_{ij} = e^{−2J_{ij}}` (`J ≥ 0` ferromagnetic) and `z_k = e^{−2h_k}`, this is the partition
function at fields `h_k`.

* **Asano's lemma** (`asano`). If `A + Bx + Cy + Dxy` has no zero on the open bidisc, then neither
  does `A + Dx` on the open disc. Proof: `A + (B+C)r + Dr²` has root product `A/D`, so a zero
  `−A/D` inside the disc would give a diagonal zero `(r, r)` inside the bidisc.
* **Two sites** (`two_site`). `|1 + ax|² − |a + x|² = (1 − a²)(1 − |x|²) ≥ 0`.
* **One bond** (`edge_contract`, `LYProp.edge`). Multiplying the two-site polynomial of a new bond
  on fresh variables and contracting twice with Asano's lemma turns `α + βx + γy + εxy` into
  `α + aβx + aγy + εxy`.

**Theorem** (`leeYang_polydisc`). `Z` has no zero on the open unit polydisc. By complement symmetry
(`maEval_eq_prod_mul_inv`) it has none outside the closed polydisc either (`leeYang_exterior`). On
the diagonal every zero lies on the unit circle (`leeYang_circle`). For fields `e^{−itλ_k}` with
`λ_k > 0`, every zero in `t` is real (`leeYang_exp_ne_zero`).
-/

open Complex Finset

namespace GaloisForLFunctions.HTGeometry.LeeYang

/-- **Asano's lemma.** If `A + Bx + Cy + Dxy` has no zero on the open bidisc, then `A + Dx` has
no zero on the open disc. -/
theorem asano {A B C D : ℂ}
    (h : ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 → A + B * x + C * y + D * x * y ≠ 0) :
    ∀ x : ℂ, ‖x‖ < 1 → A + D * x ≠ 0 := by
  have hA : A ≠ 0 := by simpa using h 0 0 (by simp) (by simp)
  intro x hx hAx
  have hD : D ≠ 0 := by
    rintro rfl; apply hA; simpa using hAx
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((B + C) ^ 2 - 4 * D * A)
  set r₁ := (-(B + C) + s) / (2 * D)
  set r₂ := (-(B + C) - s) / (2 * D)
  have hD2 : (2 : ℂ) * D ≠ 0 := mul_ne_zero two_ne_zero hD
  have h4D : (4 : ℂ) * D ≠ 0 := mul_ne_zero (by norm_num) hD
  have hr₁ : 2 * D * r₁ = -(B + C) + s := by simp only [r₁]; field_simp
  have hr₂ : 2 * D * r₂ = -(B + C) - s := by simp only [r₂]; field_simp
  have hquad : ∀ r, 4 * D * (A + B * r + C * r + D * r * r) =
      (2 * D * r) ^ 2 + 2 * (B + C) * (2 * D * r) + 4 * D * A := fun r => by ring
  have hroot : ∀ r, (r = r₁ ∨ r = r₂) → A + B * r + C * r + D * r * r = 0 := by
    rintro r (rfl | rfl)
    · refine (mul_eq_zero.mp ?_).resolve_left h4D
      rw [hquad, hr₁]; linear_combination -hs
    · refine (mul_eq_zero.mp ?_).resolve_left h4D
      rw [hquad, hr₂]; linear_combination -hs
  have hprod : r₁ * r₂ = -x := by
    have e : (2 * D * r₁) * (2 * D * r₂) = 4 * D * A := by
      rw [hr₁, hr₂]; linear_combination hs
    have e2 : (4 * D * D) * (r₁ * r₂) = (4 * D * D) * (-x) := by
      linear_combination e + 4 * D * hAx
    exact mul_left_cancel₀ (mul_ne_zero h4D hD) e2
  have hnorm : ‖r₁‖ * ‖r₂‖ < 1 := by
    rw [← norm_mul, hprod, norm_neg]; exact hx
  by_cases h1 : ‖r₁‖ < 1
  · exact h r₁ r₁ h1 h1 (hroot r₁ (Or.inl rfl))
  · have h2 : ‖r₂‖ < 1 := by
      push Not at h1
      by_contra h2; push Not at h2
      nlinarith [norm_nonneg r₁, norm_nonneg r₂]
    exact h r₂ r₂ h2 h2 (hroot r₂ (Or.inr rfl))

/-- **Two sites.** For a real coupling `|a| ≤ 1`, `1 + ax + ay + xy` has no zero on the open
bidisc. -/
theorem two_site {a : ℝ} (ha : |a| ≤ 1) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    1 + (a : ℂ) * x + (a : ℂ) * y + x * y ≠ 0 := by
  intro h
  have key : ‖1 + (a : ℂ) * x‖ ^ 2 - ‖(a : ℂ) + x‖ ^ 2 = (1 - a ^ 2) * (1 - ‖x‖ ^ 2) := by
    have h1 : ‖1 + (a : ℂ) * x‖ ^ 2 = (1 + a * x.re) ^ 2 + (a * x.im) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    have h2 : ‖(a : ℂ) + x‖ ^ 2 = (a + x.re) ^ 2 + x.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    have h3 : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [h1, h2, h3]; ring
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [abs_nonneg a, sq_abs a]
  have hx2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  have hge : ‖(a : ℂ) + x‖ ≤ ‖1 + (a : ℂ) * x‖ := by
    have : 0 ≤ (1 - a ^ 2) * (1 - ‖x‖ ^ 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith [norm_nonneg ((a : ℂ) + x), norm_nonneg (1 + (a : ℂ) * x)]
  have heq : y * ((a : ℂ) + x) = -(1 + (a : ℂ) * x) := by linear_combination h
  have hn : ‖y‖ * ‖(a : ℂ) + x‖ = ‖1 + (a : ℂ) * x‖ := by
    rw [← norm_mul, heq, norm_neg]
  by_cases hz : ‖(a : ℂ) + x‖ = 0
  · rw [hz, mul_zero] at hn
    have h1 : 1 + (a : ℂ) * x = 0 := norm_eq_zero.mp hn.symm
    have h2 : (a : ℂ) + x = 0 := norm_eq_zero.mp hz
    have hxa : x = -(a : ℂ) := by linear_combination h2
    rw [hxa] at h1 hx
    have hc : (((1 - a ^ 2 : ℝ)) : ℂ) = 0 := by push_cast; linear_combination h1
    have ha' : 1 - a ^ 2 = 0 := by exact_mod_cast hc
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at hx
    nlinarith [sq_abs a, abs_nonneg a]
  · have hpos : 0 < ‖(a : ℂ) + x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have : ‖y‖ * ‖(a : ℂ) + x‖ < ‖(a : ℂ) + x‖ := by nlinarith
    linarith

/-- **Edge contraction.** If `α + βx + γy + εxy` has no zero on the open bidisc and `|a| ≤ 1`, the
same holds for `α + aβx + aγy + εxy`. -/
theorem edge_contract {α β γ ε : ℂ} {a : ℝ} (ha : |a| ≤ 1)
    (h : ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 → α + β * x + γ * y + ε * x * y ≠ 0) :
    ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 → α + a * β * x + a * γ * y + ε * x * y ≠ 0 := by
  -- first contraction: the two copies of the first site
  have h1 : ∀ y y' : ℂ, ‖y‖ < 1 → ‖y'‖ < 1 → ∀ x : ℂ, ‖x‖ < 1 →
      (α + γ * y) * (1 + a * y') + (β + ε * y) * (a + y') * x ≠ 0 := by
    intro y y' hy hy'
    refine asano (A := (α + γ * y) * (1 + a * y')) (B := (β + ε * y) * (1 + a * y'))
      (C := (α + γ * y) * (a + y')) (D := (β + ε * y) * (a + y')) ?_
    intro x x' hx hx'
    have e : (α + γ * y) * (1 + a * y') + (β + ε * y) * (1 + a * y') * x +
        (α + γ * y) * (a + y') * x' + (β + ε * y) * (a + y') * x * x' =
        (α + β * x + γ * y + ε * x * y) * (1 + a * x' + a * y' + x' * y') := by ring
    rw [e]
    exact mul_ne_zero (h x y hx hy) (two_site ha hx' hy')
  -- second contraction: the two copies of the second site
  intro x y hx hy
  have h2 := asano (A := α + a * β * x) (B := γ + a * ε * x) (C := a * α + β * x)
    (D := a * γ + ε * x) (fun y y' hy hy' => by
      have e : α + a * β * x + (γ + a * ε * x) * y + (a * α + β * x) * y' +
          (a * γ + ε * x) * y * y' =
          (α + γ * y) * (1 + a * y') + (β + ε * y) * (a + y') * x := by ring
      rw [e]; exact h1 y y' hy hy' x hx) y hy
  have e : α + a * β * x + (a * γ + ε * x) * y = α + a * β * x + a * γ * y + ε * x * y := by ring
  rwa [e] at h2

/-! ## Multiaffine polynomials -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The multiaffine polynomial `Σ_S c_S ∏_{k∈S} z_k`. -/
def maEval (c : Finset V → ℂ) (z : V → ℂ) : ℂ := ∑ S : Finset V, c S * ∏ k ∈ S, z k

/-- `z` lies in the open unit polydisc. -/
def InDisc (z : V → ℂ) : Prop := ∀ k, ‖z k‖ < 1

/-- The Lee–Yang property: no zero on the open unit polydisc. -/
def LYProp (c : Finset V → ℂ) : Prop := ∀ z, InDisc z → maEval c z ≠ 0

/-- The coefficient with the two variables `i, j` removed. -/
def restTerm (c : Finset V → ℂ) (z : V → ℂ) (i j : V) (S : Finset V) : ℂ :=
  c S * ∏ k ∈ (S.erase i).erase j, z k

/-- The four slices of a multiaffine polynomial with respect to two variables. -/
def maSlice (c : Finset V → ℂ) (z : V → ℂ) (i j : V) (pi pj : Bool) : ℂ :=
  ∑ S : Finset V, if (decide (i ∈ S) = pi ∧ decide (j ∈ S) = pj) then restTerm c z i j S else 0

omit [Fintype V] in
theorem prod_split {i j : V} (hij : i ≠ j) (S : Finset V) (w : V → ℂ) :
    ∏ k ∈ S, w k = (∏ k ∈ (S.erase i).erase j, w k) * (if i ∈ S then w i else 1) *
      (if j ∈ S then w j else 1) := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · have hj' : j ∈ S.erase i := Finset.mem_erase.mpr ⟨fun h => hij h.symm, hj⟩
    rw [if_pos hi, if_pos hj, mul_assoc, mul_comm _ (w j), ← mul_assoc,
      mul_comm _ (w j), Finset.mul_prod_erase _ _ hj', mul_comm, Finset.mul_prod_erase _ _ hi]
  · rw [if_pos hi, if_neg hj, mul_one, Finset.erase_eq_of_notMem
      (fun h => hj (Finset.mem_of_mem_erase h)), mul_comm, Finset.mul_prod_erase _ _ hi]
  · rw [if_neg hi, if_pos hj, mul_one, Finset.erase_eq_of_notMem hi, mul_comm,
      Finset.mul_prod_erase _ _ hj]
  · rw [if_neg hi, if_neg hj, mul_one, mul_one, Finset.erase_eq_of_notMem hi,
      Finset.erase_eq_of_notMem hj]

omit [Fintype V] in
theorem prod_erase_eq {i j : V} (S : Finset V) {z w : V → ℂ}
    (hw : ∀ k, k ≠ i → k ≠ j → w k = z k) :
    ∏ k ∈ (S.erase i).erase j, w k = ∏ k ∈ (S.erase i).erase j, z k := by
  refine Finset.prod_congr rfl fun k hk => ?_
  have hkj := Finset.ne_of_mem_erase hk
  have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
  exact hw k hki hkj

/-- **Two-variable decomposition.** -/
theorem maEval_decomp {i j : V} (hij : i ≠ j) (c : Finset V → ℂ) (z w : V → ℂ)
    (hw : ∀ k, k ≠ i → k ≠ j → w k = z k) :
    maEval c w = maSlice c z i j false false + maSlice c z i j true false * w i +
      maSlice c z i j false true * w j + maSlice c z i j true true * w i * w j := by
  simp only [maSlice, Finset.sum_mul, ← Finset.sum_add_distrib, maEval]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [prod_split hij S w, prod_erase_eq S hw]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj, restTerm] <;> ring

/-- The weight of one bond: `a` if the bond crosses `S`, else `1`. -/
def bondWeight (a : ℝ) (i j : V) (S : Finset V) : ℂ := if (i ∈ S ↔ j ∈ S) then 1 else (a : ℂ)

theorem maSlice_bond {i j : V} (c : Finset V → ℂ) (z : V → ℂ) (a : ℝ) (pi pj : Bool) :
    maSlice (fun S => c S * bondWeight a i j S) z i j pi pj =
      (if pi = pj then 1 else (a : ℂ)) * maSlice c z i j pi pj := by
  simp only [maSlice, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : decide (i ∈ S) = pi ∧ decide (j ∈ S) = pj
  · rw [if_pos h, if_pos h]
    obtain ⟨h1, h2⟩ := h
    simp only [restTerm, bondWeight]
    have e : (i ∈ S ↔ j ∈ S) ↔ pi = pj := by
      rw [← h1, ← h2]; exact decide_eq_decide.symm
    by_cases hp : pi = pj
    · rw [if_pos (e.mpr hp), if_pos hp]; ring
    · rw [if_neg (fun h => hp (e.mp h)), if_neg hp]; ring
  · rw [if_neg h, if_neg h, mul_zero]

/-- **One bond preserves the Lee–Yang property.** -/
theorem LYProp.edge {c : Finset V → ℂ} (hc : LYProp c) {i j : V} (hij : i ≠ j) {a : ℝ}
    (ha : |a| ≤ 1) : LYProp fun S => c S * bondWeight a i j S := by
  intro z hz
  have hcontract := edge_contract (α := maSlice c z i j false false)
    (β := maSlice c z i j true false) (γ := maSlice c z i j false true)
    (ε := maSlice c z i j true true) ha (fun x y hx hy => by
      set w := Function.update (Function.update z i x) j y
      have hwi : w i = x := by simp [w, hij]
      have hwj : w j = y := by simp [w]
      have hwk : ∀ k, k ≠ i → k ≠ j → w k = z k := fun k hki hkj => by
        simp [w, hki, hkj]
      have hd : InDisc w := fun k => by
        by_cases hkj : k = j
        · subst hkj; rw [hwj]; exact hy
        by_cases hki : k = i
        · subst hki; rw [hwi]; exact hx
        rw [hwk k hki hkj]; exact hz k
      have := hc w hd
      rwa [maEval_decomp hij c z w hwk, hwi, hwj] at this)
    (z i) (z j) (hz i) (hz j)
  rw [maEval_decomp hij _ z z (fun _ _ _ => rfl), maSlice_bond, maSlice_bond, maSlice_bond, maSlice_bond]
  simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, one_mul]
  convert hcontract using 1

/-! ## The Lee–Yang theorem -/

/-- The ferromagnetic Ising coefficient `∏_{(i,j) ∈ E} (a_{ij} if the bond crosses S, else 1)`. -/
def isingCoeff (a : V → V → ℝ) (E : Finset (V × V)) (S : Finset V) : ℂ :=
  ∏ p ∈ E, bondWeight (a p.1 p.2) p.1 p.2 S

omit [DecidableEq V] in
theorem maEval_one (z : V → ℂ) : maEval (fun _ => (1 : ℂ)) z = ∏ k, (1 + z k) := by
  rw [maEval, Finset.prod_one_add, Finset.powerset_univ]
  simp

/-- **The Lee–Yang theorem.** For bonds `E` between distinct sites with real couplings
`|a_{ij}| ≤ 1`, the Ising polynomial `Σ_S ∏_{k∈S} z_k ∏_{(i,j)∈E} a_{ij}^{[bond crosses S]}` has no
zero on the open unit polydisc. -/
theorem leeYang_polydisc (a : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (ha : ∀ p ∈ E, |a p.1 p.2| ≤ 1) : LYProp (isingCoeff a E) := by
  induction E using Finset.induction_on with
  | empty =>
    intro z hz
    have e : isingCoeff a ∅ = fun _ => (1 : ℂ) := by funext S; simp [isingCoeff]
    rw [e, maEval_one]
    refine Finset.prod_ne_zero_iff.mpr fun k _ h => ?_
    have : z k = -1 := by linear_combination h
    have := hz k
    rw [‹z k = -1›, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  | insert p E hp ih =>
    have e : isingCoeff a (insert p E) =
        fun S => isingCoeff a E S * bondWeight (a p.1 p.2) p.1 p.2 S := by
      funext S; rw [isingCoeff, Finset.prod_insert hp, mul_comm]; rfl
    rw [e]
    exact (ih (fun q hq => hE q (Finset.mem_insert_of_mem hq))
      (fun q hq => ha q (Finset.mem_insert_of_mem hq))).edge
      (hE p (Finset.mem_insert_self p E)) (ha p (Finset.mem_insert_self p E))

/-! ## The exterior and the circle -/

theorem bondWeight_compl (a : ℝ) (i j : V) (S : Finset V) :
    bondWeight a i j Sᶜ = bondWeight a i j S := by
  simp only [bondWeight, Finset.mem_compl, not_iff_not]

theorem isingCoeff_compl (a : V → V → ℝ) (E : Finset (V × V)) (S : Finset V) :
    isingCoeff a E Sᶜ = isingCoeff a E S := by
  simp only [isingCoeff, bondWeight_compl]

/-- **Complement symmetry.** For complement-invariant coefficients,
`P(z) = (∏_k z_k)·P(1/z)`. -/
theorem maEval_eq_prod_mul_inv {c : Finset V → ℂ} (hc : ∀ S, c Sᶜ = c S) {z : V → ℂ}
    (hz : ∀ k, z k ≠ 0) : maEval c z = (∏ k, z k) * maEval c fun k => (z k)⁻¹ := by
  have hcompl : maEval c z = ∑ S : Finset V, c Sᶜ * ∏ k ∈ Sᶜ, z k := by
    rw [maEval]
    exact Fintype.sum_equiv ⟨compl, compl, compl_compl, compl_compl⟩ _ _ (fun S => by
      simp only [Equiv.coe_fn_mk, compl_compl])
  rw [hcompl, maEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [hc S]
  have hS : ∏ k ∈ S, z k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hz k
  have h := Finset.prod_compl_mul_prod S z
  have hinv : ∏ k ∈ S, (z k)⁻¹ = (∏ k ∈ S, z k)⁻¹ := Finset.prod_inv_distrib z
  rw [hinv, ← h]
  field_simp

/-- **The Lee–Yang theorem outside the polydisc.** -/
theorem leeYang_exterior (a : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (ha : ∀ p ∈ E, |a p.1 p.2| ≤ 1) {z : V → ℂ} (hz : ∀ k, 1 < ‖z k‖) :
    maEval (isingCoeff a E) z ≠ 0 := by
  have hz0 : ∀ k, z k ≠ 0 := fun k h => by have := hz k; rw [h, norm_zero] at this; linarith
  rw [maEval_eq_prod_mul_inv (isingCoeff_compl a E) hz0]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hz0 k) (leeYang_polydisc a E hE ha _ fun k => ?_)
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ (hz k)

/-- **The Lee–Yang circle theorem.** On the diagonal, every zero has modulus one. -/
theorem leeYang_circle (a : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (ha : ∀ p ∈ E, |a p.1 p.2| ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ ≠ 1) :
    maEval (isingCoeff a E) (fun _ => ζ) ≠ 0 := by
  rcases lt_or_gt_of_ne hζ with h | h
  · exact leeYang_polydisc a E hE ha _ fun _ => h
  · exact leeYang_exterior a E hE ha fun _ => h

/-- **Real zeros for positive fields.** With fields `e^{−itλ_k}`, `λ_k > 0`, the partition
function of every ferromagnetic graph has only real zeros in `t`. -/
theorem leeYang_exp_ne_zero (a : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (ha : ∀ p ∈ E, |a p.1 p.2| ≤ 1) {lam : V → ℝ} (hlam : ∀ k, 0 < lam k) {t : ℂ}
    (ht : t.im ≠ 0) :
    maEval (isingCoeff a E) (fun k => Complex.exp (-(I * t * (lam k : ℂ)))) ≠ 0 := by
  have hn : ∀ k, ‖Complex.exp (-(I * t * (lam k : ℂ)))‖ = Real.exp (lam k * t.im) := by
    intro k
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rcases lt_or_gt_of_ne ht with h | h
  · refine leeYang_polydisc a E hE ha _ fun k => ?_
    rw [hn k, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (hlam k) h
  · refine leeYang_exterior a E hE ha fun k => ?_
    rw [hn k, Real.one_lt_exp_iff]
    exact mul_pos (hlam k) h

end GaloisForLFunctions.HTGeometry.LeeYang
