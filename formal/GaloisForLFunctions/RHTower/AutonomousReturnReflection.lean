import GaloisForLFunctions.HTGeometry.GappedEigenlineTimeUniformFloor

/-!
# Reflection of robust circuit complexity across an autonomous return

The normalized Choi vector turns a unitary into a pure state, and the projective distance between
two such states is the trace distance of the corresponding Choi states.  That distance is
bi-invariant and invariant under simultaneous inversion, because both operations leave the modulus
of the normalized Hilbert--Schmidt pairing unchanged.

An inverse-closed gate dictionary therefore has an inversion-invariant word cost, and the group law
of a one-parameter evolution places the two endpoints of a return cycle at exactly the return defect
from each other.  Robust complexity and every circuit-length incidence shell are consequently
reflected about the midpoint of the cycle, up to that defect.
-/

open scoped BigOperators ENNReal
open Matrix

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

open _root_.RHTower _root_.HTGeometry

section ChoiDistance

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The normalized Choi vector of a matrix. -/
noncomputable def choiVector (U : Matrix n n ℂ) : EuclideanSpace ℂ (n × n) :=
  WithLp.toLp 2 (fun p : n × n => U p.1 p.2 / Real.sqrt (Fintype.card n))

omit [DecidableEq n] in
theorem trace_conjTranspose_mul (U V : Matrix n n ℂ) :
    Matrix.trace (Uᴴ * V) = ∑ i : n, ∑ j : n, (starRingEnd ℂ) (U i j) * V i j := by
  classical
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

omit [DecidableEq n] in
theorem trace_conjTranspose_mul_prod (U V : Matrix n n ℂ) :
    Matrix.trace (Uᴴ * V) = ∑ p : n × n, (starRingEnd ℂ) (U p.1 p.2) * V p.1 p.2 := by
  rw [trace_conjTranspose_mul, ← Finset.sum_product', Finset.univ_product_univ]

omit [DecidableEq n] in
theorem inner_choiVector (hn : 0 < Fintype.card n) (U V : Matrix n n ℂ) :
    (inner ℂ (choiVector U) (choiVector V) : ℂ) =
      Matrix.trace (Uᴴ * V) / (Fintype.card n : ℂ) := by
  classical
  have hpos : (0 : ℝ) < Fintype.card n := by exact_mod_cast hn
  have hsqrt : (Real.sqrt (Fintype.card n) : ℂ) * (Real.sqrt (Fintype.card n) : ℂ) =
      (Fintype.card n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
    norm_cast
  have hne : (Real.sqrt (Fintype.card n) : ℂ) ≠ 0 := by
    simpa using Real.sqrt_ne_zero'.mpr hpos
  have hsum : (inner ℂ (choiVector U) (choiVector V) : ℂ) =
      ∑ p : n × n, (starRingEnd ℂ) (U p.1 p.2 / (Real.sqrt (Fintype.card n) : ℂ)) *
        (V p.1 p.2 / (Real.sqrt (Fintype.card n) : ℂ)) := by
    simp [PiLp.inner_apply, RCLike.inner_apply, choiVector]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  have hterm : ∀ p : n × n,
      (starRingEnd ℂ) (U p.1 p.2 / (Real.sqrt (Fintype.card n) : ℂ)) *
        (V p.1 p.2 / (Real.sqrt (Fintype.card n) : ℂ)) =
      ((starRingEnd ℂ) (U p.1 p.2) * V p.1 p.2) / (Fintype.card n : ℂ) := by
    intro p
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, hsqrt]
  rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.sum_div, ← trace_conjTranspose_mul_prod]

theorem norm_choiVector_eq_one (hn : 0 < Fintype.card n) {U : Matrix n n ℂ}
    (hU : Uᴴ * U = 1) : ‖choiVector U‖ = 1 := by
  have hinner := inner_choiVector hn U U
  rw [hU, Matrix.trace_one] at hinner
  have hcard : ((Fintype.card n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hone : (inner ℂ (choiVector U) (choiVector U) : ℂ) = 1 := by
    rw [hinner, div_self hcard]
  have hnorm : ‖choiVector U‖ ^ 2 = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (choiVector U)
    rw [hone] at h
    have hcast : ((‖choiVector U‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      exact h.symm
    exact_mod_cast hcast
  nlinarith [norm_nonneg (choiVector U), hnorm]

/-- The projective Choi distance between two unitaries. -/
noncomputable def choiDist (U V : Matrix n n ℂ) : ℝ :=
  pureStateTraceDistance (choiVector U) (choiVector V)

theorem choiDist_eq (hn : 0 < Fintype.card n) (U V : Matrix n n ℂ) :
    choiDist U V = Real.sqrt (1 - (‖Matrix.trace (Uᴴ * V)‖ / Fintype.card n) ^ 2) := by
  have hpos : (0 : ℝ) < Fintype.card n := by exact_mod_cast hn
  rw [choiDist, pureStateTraceDistance, inner_choiVector hn, norm_div]
  congr 2
  simp

theorem choiDist_nonneg (U V : Matrix n n ℂ) : 0 ≤ choiDist U V :=
  pureStateTraceDistance_nonneg _ _

theorem choiDist_comm (U V : Matrix n n ℂ) : choiDist U V = choiDist V U :=
  pureStateTraceDistance_comm _ _

theorem choiDist_self (hn : 0 < Fintype.card n) {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    choiDist U U = 0 := by
  have hnorm := norm_choiVector_eq_one hn hU
  have hinner : ‖(inner ℂ (choiVector U) (choiVector U) : ℂ)‖ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hnorm]
    simp
  rw [choiDist, pureStateTraceDistance, hinner]
  simp

theorem choiDist_triangle (hn : 0 < Fintype.card n) {U V W : Matrix n n ℂ}
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) :
    choiDist U W ≤ choiDist U V + choiDist V W :=
  pureStateTraceDistance_triangle _ _ _ (norm_choiVector_eq_one hn hU)
    (norm_choiVector_eq_one hn hV) (norm_choiVector_eq_one hn hW)

theorem choiDist_left_mul (hn : 0 < Fintype.card n) {A : Matrix n n ℂ} (hA : Aᴴ * A = 1)
    (U V : Matrix n n ℂ) : choiDist (A * U) (A * V) = choiDist U V := by
  have htrace : Matrix.trace ((A * U)ᴴ * (A * V)) = Matrix.trace (Uᴴ * V) := by
    rw [Matrix.conjTranspose_mul]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ A V, hA, Matrix.one_mul]
  rw [choiDist_eq hn, choiDist_eq hn, htrace]

theorem choiDist_right_mul (hn : 0 < Fintype.card n) {A : Matrix n n ℂ} (hA : A * Aᴴ = 1)
    (U V : Matrix n n ℂ) : choiDist (U * A) (V * A) = choiDist U V := by
  have htrace : Matrix.trace ((U * A)ᴴ * (V * A)) = Matrix.trace (Uᴴ * V) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc, hA, Matrix.mul_one]
  rw [choiDist_eq hn, choiDist_eq hn, htrace]

theorem choiDist_conjTranspose (hn : 0 < Fintype.card n) (U V : Matrix n n ℂ) :
    choiDist Uᴴ Vᴴ = choiDist U V := by
  have hstar : Matrix.trace ((Uᴴ)ᴴ * Vᴴ) =
      (starRingEnd ℂ) (Matrix.trace (Uᴴ * V)) := by
    have h1 : (starRingEnd ℂ) (Matrix.trace (Uᴴ * V)) = Matrix.trace ((Uᴴ * V)ᴴ) :=
      (Matrix.trace_conjTranspose (Uᴴ * V)).symm
    rw [Matrix.conjTranspose_conjTranspose, h1, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  rw [choiDist_eq hn, choiDist_eq hn, hstar, RCLike.norm_conj]

end ChoiDistance

section GateWords

variable {n : Type*} [Fintype n] [DecidableEq n] {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- The matrix realized by a gate word. -/
def wordProd (dict : Γ → Matrix n n ℂ) (w : List Γ) : Matrix n n ℂ := (w.map dict).prod

@[simp] theorem wordProd_nil (dict : Γ → Matrix n n ℂ) : wordProd dict [] = 1 := rfl

@[simp] theorem wordProd_cons (dict : Γ → Matrix n n ℂ) (g : Γ) (w : List Γ) :
    wordProd dict (g :: w) = dict g * wordProd dict w := rfl

/-- Reversing a word and replacing every gate by its inverse conjugates the word matrix. -/
theorem wordProd_inverseWord (dict : Γ → Matrix n n ℂ) (inv : Γ → Γ)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ) (w : List Γ) :
    wordProd dict ((w.map inv).reverse) = (wordProd dict w)ᴴ := by
  induction w with
  | nil => simp [wordProd]
  | cons g w ih =>
    have hmap : ((g :: w).map inv).reverse = (w.map inv).reverse ++ [inv g] := by
      simp
    rw [hmap, wordProd, List.map_append, List.prod_append, ← wordProd, ← wordProd, ih]
    simp [hinv g, Matrix.conjTranspose_mul]

theorem wordProd_unitary (dict : Γ → Matrix n n ℂ) (hdict : ∀ g, (dict g)ᴴ * dict g = 1)
    (w : List Γ) : (wordProd dict w)ᴴ * wordProd dict w = 1 := by
  induction w with
  | nil => simp [wordProd]
  | cons g u ih =>
    rw [wordProd_cons, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (dict g)ᴴ, hdict g, Matrix.one_mul, ih]

theorem length_inverseWord (inv : Γ → Γ) (w : List Γ) :
    ((w.map inv).reverse).length = w.length := by
  simp

/-- Robust circuit complexity of a target at a given resolution, infinite when unreachable. -/
noncomputable def choiComplexity (dict : Γ → Matrix n n ℂ) (ε : ℝ) (U : Matrix n n ℂ) : ℕ∞ :=
  ⨅ w ∈ {w : List Γ | choiDist (wordProd dict w) U ≤ ε}, (w.length : ℕ∞)

theorem choiComplexity_le_of_word (dict : Γ → Matrix n n ℂ) (ε : ℝ) (U : Matrix n n ℂ)
    {w : List Γ} (hw : choiDist (wordProd dict w) U ≤ ε) :
    choiComplexity dict ε U ≤ (w.length : ℕ∞) := by
  refine le_trans (iInf_le _ w) ?_
  exact iInf_le (fun _ : w ∈ {w : List Γ | choiDist (wordProd dict w) U ≤ ε} =>
    (w.length : ℕ∞)) hw

theorem le_choiComplexity_iff (dict : Γ → Matrix n n ℂ) (ε : ℝ) (U : Matrix n n ℂ) (c : ℕ∞) :
    c ≤ choiComplexity dict ε U ↔
      ∀ w : List Γ, choiDist (wordProd dict w) U ≤ ε → c ≤ (w.length : ℕ∞) := by
  rw [choiComplexity, le_iInf_iff]
  constructor
  · intro h w hw
    exact le_iInf_iff.mp (h w) hw
  · intro h w
    exact le_iInf fun hw => h w hw

theorem choiComplexity_mono (dict : Γ → Matrix n n ℂ) {ε ε' : ℝ} (hε : ε ≤ ε')
    (U : Matrix n n ℂ) : choiComplexity dict ε' U ≤ choiComplexity dict ε U := by
  rw [le_choiComplexity_iff]
  intro w hw
  exact choiComplexity_le_of_word dict ε' U (le_trans hw hε)

/-- The incidence shell of a fixed circuit length. -/
noncomputable def shellIncidence (dict : Γ → Matrix n n ℂ) (ε : ℝ) (ℓ : ℕ)
    (U : Matrix n n ℂ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun w : List.Vector Γ ℓ =>
    choiDist (wordProd dict w.1) U ≤ ε).card : ℝ) / (Fintype.card Γ : ℝ) ^ ℓ

end GateWords

section Reflection

variable {n : Type*} [Fintype n] [DecidableEq n] {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

variable (dict : Γ → Matrix n n ℂ) (inv : Γ → Γ) (Uev : ℝ → Matrix n n ℂ)

theorem unitary_mul_conjTranspose {A : Matrix n n ℂ} (hA : Aᴴ * A = 1) : A * Aᴴ = 1 :=
  mul_eq_one_comm.mp hA

theorem evolution_zero (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t)
    (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1) : Uev 0 = 1 := by
  have hsq : Uev 0 = Uev 0 * Uev 0 := by
    have := hgroup 0 0
    rwa [add_zero] at this
  have h : (Uev 0)ᴴ * Uev 0 = (Uev 0)ᴴ * (Uev 0 * Uev 0) := congrArg (fun M => (Uev 0)ᴴ * M) hsq
  rw [hunit 0, ← Matrix.mul_assoc, hunit 0, Matrix.one_mul] at h
  exact h.symm

theorem evolution_neg (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t)
    (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1) (t : ℝ) : Uev (-t) = (Uev t)ᴴ := by
  have hone : Uev t * Uev (-t) = 1 := by
    have := hgroup t (-t)
    rw [add_neg_cancel] at this
    rw [← this, evolution_zero Uev hgroup hunit]
  have h : (Uev t)ᴴ * (Uev t * Uev (-t)) = (Uev t)ᴴ * 1 := congrArg (fun M => (Uev t)ᴴ * M) hone
  rw [← Matrix.mul_assoc, hunit t, Matrix.one_mul, Matrix.mul_one] at h
  exact h

/-- The projective return defect of a proposed return time. -/
noncomputable def returnDefect (Uev : ℝ → Matrix n n ℂ) (R : ℝ) : ℝ := choiDist (Uev R) 1

/-- The two endpoints of a return cycle sit exactly at the return defect from each other. -/
theorem choiDist_evolution_reflect (hn : 0 < Fintype.card n)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (R t : ℝ) : choiDist (Uev (R - t)) (Uev (-t)) = returnDefect Uev R := by
  have hsplit : Uev (R - t) = Uev R * Uev (-t) := by
    have := hgroup R (-t)
    rwa [← sub_eq_add_neg] at this
  have hA : Uev (-t) * (Uev (-t))ᴴ = 1 := unitary_mul_conjTranspose (hunit (-t))
  have hrefl := choiDist_right_mul hn hA (Uev R) 1
  rw [returnDefect, ← hrefl, hsplit, Matrix.one_mul]

/-- A word reaching the reflected time reaches the time itself after inversion. -/
theorem choiDist_inverseWord_reflect (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) {ε R t : ℝ} {w : List Γ}
    (hw : choiDist (wordProd dict w) (Uev (R - t)) ≤ ε) :
    choiDist (wordProd dict ((w.map inv).reverse)) (Uev t) ≤ ε + returnDefect Uev R := by
  have hword : (wordProd dict w)ᴴ * wordProd dict w = 1 := wordProd_unitary dict hdict w
  have hstep : choiDist (wordProd dict w) (Uev (-t)) ≤ ε + returnDefect Uev R := by
    have htri := choiDist_triangle hn hword (hunit (R - t)) (hunit (-t))
    have hrefl := choiDist_evolution_reflect Uev hn hgroup hunit R t
    rw [hrefl] at htri
    linarith
  rw [wordProd_inverseWord dict inv hinv w]
  have hneg : Uev t = (Uev (-t))ᴴ := by
    rw [evolution_neg Uev hgroup hunit t, Matrix.conjTranspose_conjTranspose]
  rw [hneg, choiDist_conjTranspose hn]
  exact hstep

/-- A word reaching a time reaches the reflected time after inversion. -/
theorem choiDist_inverseWord_reflect' (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) {ε R t : ℝ} {w : List Γ}
    (hw : choiDist (wordProd dict w) (Uev t) ≤ ε) :
    choiDist (wordProd dict ((w.map inv).reverse)) (Uev (R - t)) ≤ ε + returnDefect Uev R := by
  have hword : (wordProd dict w)ᴴ * wordProd dict w = 1 := wordProd_unitary dict hdict w
  have hneg : Uev (-t) = (Uev t)ᴴ := evolution_neg Uev hgroup hunit t
  have hstep : choiDist (wordProd dict ((w.map inv).reverse)) (Uev (-t)) ≤ ε := by
    rw [wordProd_inverseWord dict inv hinv w, hneg, choiDist_conjTranspose hn]
    exact hw
  have hwordinv : (wordProd dict ((w.map inv).reverse))ᴴ *
      wordProd dict ((w.map inv).reverse) = 1 :=
    wordProd_unitary dict hdict _
  have htri := choiDist_triangle hn hwordinv (hunit (-t)) (hunit (R - t))
  have hrefl := choiDist_evolution_reflect Uev hn hgroup hunit R t
  rw [choiDist_comm (Uev (R - t)) (Uev (-t))] at hrefl
  rw [hrefl] at htri
  linarith

/-- **Robust recurrence reflection.**  Complexity at a time is bounded by complexity at the
reflected time, at resolution enlarged by the return defect, and conversely. -/
theorem choiComplexity_reflect (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) (ε R t : ℝ) :
    choiComplexity dict (ε + returnDefect Uev R) (Uev t) ≤
      choiComplexity dict ε (Uev (R - t)) := by
  rw [le_choiComplexity_iff]
  intro w hw
  have hinvword := choiDist_inverseWord_reflect dict inv Uev hn hinv hgroup hunit hdict hw
  refine le_trans (choiComplexity_le_of_word dict (ε + returnDefect Uev R) (Uev t) hinvword) ?_
  rw [length_inverseWord inv w]

/-- The reflected form of the recurrence reflection. -/
theorem choiComplexity_reflect' (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) (ε R t : ℝ) :
    choiComplexity dict (ε + returnDefect Uev R) (Uev (R - t)) ≤
      choiComplexity dict ε (Uev t) := by
  rw [le_choiComplexity_iff]
  intro w hw
  have hinvword := choiDist_inverseWord_reflect' dict inv Uev hn hinv hgroup hunit hdict
    (R := R) hw
  refine le_trans
    (choiComplexity_le_of_word dict (ε + returnDefect Uev R) (Uev (R - t)) hinvword) ?_
  rw [length_inverseWord inv w]

/-- **Palindromic complexity history.**  At an exact projective return the complexity history is
symmetric about the midpoint of the cycle. -/
theorem choiComplexity_eq_of_exact_return (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) {R : ℝ} (hR : returnDefect Uev R = 0) (ε t : ℝ) :
    choiComplexity dict ε (Uev (R - t)) = choiComplexity dict ε (Uev t) := by
  have h1 := choiComplexity_reflect dict inv Uev hn hinv hgroup hunit hdict ε R t
  have h2 := choiComplexity_reflect' dict inv Uev hn hinv hgroup hunit hdict ε R t
  rw [hR, add_zero] at h1 h2
  exact le_antisymm h2 h1

/-- **Growth forces the recurrence decline.**  A complexity lower bound at a time is a lower bound
at the reflected time. -/
theorem lt_choiComplexity_reflect (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) (ε R t : ℝ) {s : ℕ∞}
    (h : s < choiComplexity dict (ε + returnDefect Uev R) (Uev t)) :
    s < choiComplexity dict ε (Uev (R - t)) :=
  lt_of_lt_of_le h (choiComplexity_reflect dict inv Uev hn hinv hgroup hunit hdict ε R t)

/-- **Simulation envelopes reflect.**  A complexity upper bound at a time is an upper bound at the
reflected time, at resolution enlarged by the return defect. -/
theorem choiComplexity_reflect_le (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) (ε R t : ℝ) {s : ℕ∞}
    (h : choiComplexity dict ε (Uev t) ≤ s) :
    choiComplexity dict (ε + returnDefect Uev R) (Uev (R - t)) ≤ s :=
  le_trans (choiComplexity_reflect' dict inv Uev hn hinv hgroup hunit hdict ε R t) h

/-- The reflected sublevel set of the complexity history is contained in the enlarged one. -/
theorem sublevel_reflect_subset (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) (ε R : ℝ) (s : ℕ∞) :
    (fun t : ℝ => R - t) '' {t : ℝ | choiComplexity dict ε (Uev t) ≤ s} ⊆
      {t : ℝ | choiComplexity dict (ε + returnDefect Uev R) (Uev t) ≤ s} := by
  rintro u ⟨t, ht, rfl⟩
  exact choiComplexity_reflect_le dict inv Uev hn hinv hgroup hunit hdict ε R t ht

/-- Reversal with gatewise inversion, as a length-preserving map of word shells. -/
def inverseWordVector (inv : Γ → Γ) (ℓ : ℕ) (w : List.Vector Γ ℓ) : List.Vector Γ ℓ :=
  ⟨(w.1.map inv).reverse, by simp [w.2]⟩

theorem inverseWordVector_injective {inv : Γ → Γ} (hinvol : Function.Involutive inv) (ℓ : ℕ) :
    Function.Injective (inverseWordVector inv ℓ) := by
  intro w v h
  have h1 : (w.1.map inv).reverse = (v.1.map inv).reverse := congrArg Subtype.val h
  have h2 : w.1.map inv = v.1.map inv := List.reverse_injective h1
  have h3 : w.1 = v.1 := List.map_injective_iff.mpr hinvol.injective h2
  exact Subtype.ext h3

/-- **Every circuit-length shell is reflected.**  The incidence shell at the reflected time is
bounded by the shell at the time itself, at resolution enlarged by the return defect. -/
theorem shellIncidence_reflect (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ) (hinvol : Function.Involutive inv)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) (ε R t : ℝ) (ℓ : ℕ) :
    shellIncidence dict ε ℓ (Uev (R - t)) ≤
      shellIncidence dict (ε + returnDefect Uev R) ℓ (Uev t) := by
  classical
  have hcard : (Finset.univ.filter fun w : List.Vector Γ ℓ =>
      choiDist (wordProd dict w.1) (Uev (R - t)) ≤ ε).card ≤
      (Finset.univ.filter fun w : List.Vector Γ ℓ =>
        choiDist (wordProd dict w.1) (Uev t) ≤ ε + returnDefect Uev R).card := by
    refine Finset.card_le_card_of_injOn (inverseWordVector inv ℓ) (fun w hw => ?_)
      (fun w _ v _ h => inverseWordVector_injective hinvol ℓ h)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact choiDist_inverseWord_reflect dict inv Uev hn hinv hgroup hunit hdict
      (Finset.mem_filter.mp hw).2
  have hpow : (0 : ℝ) ≤ (Fintype.card Γ : ℝ) ^ ℓ := by positivity
  rw [shellIncidence, shellIncidence]
  gcongr

/-- The reflected form of the shell reflection. -/
theorem shellIncidence_reflect' (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ) (hinvol : Function.Involutive inv)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) (ε R t : ℝ) (ℓ : ℕ) :
    shellIncidence dict ε ℓ (Uev t) ≤
      shellIncidence dict (ε + returnDefect Uev R) ℓ (Uev (R - t)) := by
  classical
  have hcard : (Finset.univ.filter fun w : List.Vector Γ ℓ =>
      choiDist (wordProd dict w.1) (Uev t) ≤ ε).card ≤
      (Finset.univ.filter fun w : List.Vector Γ ℓ =>
        choiDist (wordProd dict w.1) (Uev (R - t)) ≤ ε + returnDefect Uev R).card := by
    refine Finset.card_le_card_of_injOn (inverseWordVector inv ℓ) (fun w hw => ?_)
      (fun w _ v _ h => inverseWordVector_injective hinvol ℓ h)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact choiDist_inverseWord_reflect' dict inv Uev hn hinv hgroup hunit hdict (R := R)
      (Finset.mem_filter.mp hw).2
  rw [shellIncidence, shellIncidence]
  gcongr

/-- At an exact projective return every incidence shell is symmetric about the midpoint. -/
theorem shellIncidence_eq_of_exact_return (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ) (hinvol : Function.Involutive inv)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) {R : ℝ} (hR : returnDefect Uev R = 0) (ε t : ℝ)
    (ℓ : ℕ) :
    shellIncidence dict ε ℓ (Uev (R - t)) = shellIncidence dict ε ℓ (Uev t) := by
  have h1 := shellIncidence_reflect dict inv Uev hn hinv hinvol hgroup hunit hdict ε R t ℓ
  have h2 := shellIncidence_reflect' dict inv Uev hn hinv hinvol hgroup hunit hdict ε R t ℓ
  rw [hR, add_zero] at h1 h2
  exact le_antisymm h1 h2

/-- The extended positive partition function of the incidence shells. -/
noncomputable def shellPartition (dict : Γ → Matrix n n ℂ) (b : ℕ → ℝ) (ε : ℝ)
    (U : Matrix n n ℂ) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, ENNReal.ofReal (b ℓ * shellIncidence dict ε ℓ U)

/-- **The complete incidence spectrum is reflected.**  Every nonnegative length weighting of the
incidence shells obeys the same reflection. -/
theorem shellPartition_reflect (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ) (hinvol : Function.Involutive inv)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) {b : ℕ → ℝ} (hb : ∀ ℓ, 0 ≤ b ℓ) (ε R t : ℝ) :
    shellPartition dict b ε (Uev (R - t)) ≤
      shellPartition dict b (ε + returnDefect Uev R) (Uev t) := by
  refine ENNReal.tsum_le_tsum fun ℓ => ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_left
    (shellIncidence_reflect dict inv Uev hn hinv hinvol hgroup hunit hdict ε R t ℓ) (hb ℓ)

/-- At an exact projective return the whole incidence spectrum is symmetric. -/
theorem shellPartition_eq_of_exact_return (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ) (hinvol : Function.Involutive inv)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) (b : ℕ → ℝ) {R : ℝ} (hR : returnDefect Uev R = 0)
    (ε t : ℝ) :
    shellPartition dict b ε (Uev (R - t)) = shellPartition dict b ε (Uev t) := by
  refine tsum_congr fun ℓ => ?_
  rw [shellIncidence_eq_of_exact_return dict inv Uev hn hinv hinvol hgroup hunit hdict hR ε t ℓ]


/-- The reflected superlevel set of the enlarged complexity history is contained in the
superlevel set at the original resolution. -/
theorem superlevel_reflect_subset (hn : 0 < Fintype.card n)
    (hinv : ∀ g, dict (inv g) = (dict g)ᴴ)
    (hgroup : ∀ s t, Uev (s + t) = Uev s * Uev t) (hunit : ∀ t, (Uev t)ᴴ * Uev t = 1)
    (hdict : ∀ g, (dict g)ᴴ * dict g = 1) (ε R : ℝ) (s : ℕ∞) :
    (fun t : ℝ => R - t) ''
        {t : ℝ | ¬ choiComplexity dict (ε + returnDefect Uev R) (Uev t) ≤ s} ⊆
      {t : ℝ | ¬ choiComplexity dict ε (Uev t) ≤ s} := by
  rintro u ⟨t, ht, rfl⟩
  intro hc
  exact ht (le_trans (choiComplexity_reflect dict inv Uev hn hinv hgroup hunit hdict ε R t) hc)


end Reflection

end GaloisForLFunctions.RHTower
