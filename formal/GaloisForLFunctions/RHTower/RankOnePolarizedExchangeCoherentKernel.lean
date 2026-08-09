import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeCurvature
import Mathlib.CategoryTheory.SingleObj

/-!
# Maximal coherent framed subspace of the polarized exchange family

The common kernel of all pairwise exchange curvatures is the maximal framed subspace on which the
polarized transport composes.  It is everything at the trivial character and the permanent conormal
line otherwise, so the coherent framed dimension jumps from one to two exactly at triviality.

The permanent line is invariant, and the restricted family is a genuine monoid representation.
Consequently no strict reassociation defect of any longer word adds a new condition: the common
kernel of all word defects equals the pairwise one.

Finally, a polarized family that factors through any categorical realization of the multiplication
monoid is forced to be a monoid representation, hence to have trivial character.
-/

namespace RHTower

noncomputable section

open Matrix

variable {k : Type*} [Field k]

/-! ## The permanent conormal line -/

variable (k) in
/-- The permanent conormal line: the kernel of the single exchange defect direction. -/
def permanentLine : Submodule k (Fin 2 → k) :=
  LinearMap.ker (Matrix.mulVecLin (exchangeE12 k))

theorem exchangeE12_mulVec (v : Fin 2 → k) : Matrix.mulVec (exchangeE12 k) v = ![v 1, 0] := by
  funext i
  fin_cases i
  all_goals simp [exchangeE12, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem mem_permanentLine_iff {v : Fin 2 → k} : v ∈ permanentLine k ↔ v 1 = 0 := by
  rw [permanentLine, LinearMap.mem_ker, Matrix.mulVecLin_apply, exchangeE12_mulVec]
  constructor
  · intro h
    have := congrFun h 0
    simpa using this
  · intro h
    funext i
    fin_cases i <;> simp [h]

theorem permanentLine_eq_span : permanentLine k = Submodule.span k {![(1 : k), 0]} := by
  ext v
  rw [mem_permanentLine_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [h]
  · rintro ⟨c, rfl⟩
    simp

theorem permanentLine_lt_top : permanentLine k < (⊤ : Submodule k (Fin 2 → k)) := by
  refine lt_of_le_of_ne le_top ?_
  intro h
  have hmem : ![(0 : k), 1] ∈ permanentLine k := by rw [h]; trivial
  rw [mem_permanentLine_iff] at hmem
  simp at hmem

theorem ker_smul_exchangeE12 {c : k} (hc : c ≠ 0) :
    LinearMap.ker (Matrix.mulVecLin (c • exchangeE12 k)) = permanentLine k := by
  ext v
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.smul_mulVec,
    exchangeE12_mulVec, mem_permanentLine_iff]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Pi.smul_apply, Matrix.cons_val_zero, Pi.zero_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left hc
  · intro h
    funext i
    fin_cases i <;> simp [h]

theorem range_smul_exchangeE12 {c : k} (hc : c ≠ 0) :
    LinearMap.range (Matrix.mulVecLin (c • exchangeE12 k)) = permanentLine k := by
  ext w
  rw [LinearMap.mem_range, mem_permanentLine_iff]
  constructor
  · rintro ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.smul_mulVec, exchangeE12_mulVec]
    simp
  · intro h
    refine ⟨![0, c⁻¹ * w 0], ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.smul_mulVec, exchangeE12_mulVec]
    funext i
    fin_cases i <;> simp [mul_inv_cancel_left₀ hc, h]

/-! ## The maximal coherent framed subspace -/

/-- The maximal coherent framed subspace: the common kernel of every pairwise exchange
curvature. -/
def coherentKernel (χ : ℕ+ →* kˣ) : Submodule k (Fin 2 → k) :=
  ⨅ m : ℕ+, ⨅ n : ℕ+, LinearMap.ker (Matrix.mulVecLin (exchangeCurvature χ m n))

theorem mem_coherentKernel_iff {χ : ℕ+ →* kˣ} {v : Fin 2 → k} :
    v ∈ coherentKernel χ ↔ ∀ m n : ℕ+, Matrix.mulVec (exchangeCurvature χ m n) v = 0 := by
  simp only [coherentKernel, Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply]

/-- **At the trivial character the whole frame is coherent.** -/
theorem coherentKernel_one : coherentKernel (1 : ℕ+ →* kˣ) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  rw [mem_coherentKernel_iff]
  intro m n
  rw [exchangeCurvature_eq]
  simp

/-- **Off the trivial character only the permanent conormal line is coherent.** -/
theorem coherentKernel_of_ne_one {χ : ℕ+ →* kˣ} (h : χ ≠ 1) :
    coherentKernel χ = permanentLine k := by
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ+, χ n ≠ 1 := by
    by_contra hc
    exact h (MonoidHom.ext fun n => not_not.1 fun hn => hc ⟨n, hn⟩)
  have hc : (χ 2 : k) * (1 - (χ n₀ : k)) ≠ 0 := by
    refine mul_ne_zero (Units.ne_zero (χ 2)) ?_
    intro hz
    exact hn₀ (Units.ext (by simp only [Units.val_one]; linear_combination -hz))
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [mem_coherentKernel_iff] at hv
    have h2 := hv 2 n₀
    rw [exchangeCurvature_two] at h2
    rw [← ker_smul_exchangeE12 hc, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact h2
  · intro v hv
    rw [mem_coherentKernel_iff]
    intro m n
    rw [exchangeCurvature_eq, Matrix.smul_mulVec, exchangeE12_mulVec,
      mem_permanentLine_iff.1 hv]
    simp

/-- The permanent conormal line is invariant under the polarized transport. -/
theorem permanentLine_invariant (χ : ℕ+ →* kˣ) {v : Fin 2 → k} (hv : v ∈ permanentLine k)
    (n : ℕ+) : Matrix.mulVec (exchangeTransport χ n) v ∈ permanentLine k := by
  rw [mem_permanentLine_iff] at hv ⊢
  simp [exchangeTransport, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hv]

/-- **The coherent subspace carries a genuine monoid representation.** -/
theorem coherentKernel_isRep {χ : ℕ+ →* kˣ} {v : Fin 2 → k} (hv : v ∈ coherentKernel χ)
    (m n : ℕ+) :
    Matrix.mulVec (exchangeTransport χ m) (Matrix.mulVec (exchangeTransport χ n) v) =
      Matrix.mulVec (exchangeTransport χ (m * n)) v := by
  have h := mem_coherentKernel_iff.1 hv m n
  rw [exchangeCurvature, Matrix.sub_mulVec, sub_eq_zero, ← Matrix.mulVec_mulVec] at h
  exact h

/-! ## Higher-word defects add nothing -/

/-- The transport of a word of degrees. -/
def wordTransport (χ : ℕ+ →* kˣ) (l : List ℕ+) : Matrix (Fin 2) (Fin 2) k :=
  (l.map (exchangeTransport χ)).prod

/-- The reassociation defect of a word of degrees. -/
def wordDefect (χ : ℕ+ →* kˣ) (l : List ℕ+) : Matrix (Fin 2) (Fin 2) k :=
  wordTransport χ l - exchangeTransport χ l.prod

/-- The common kernel of every word defect. -/
def wordKernel (χ : ℕ+ →* kˣ) : Submodule k (Fin 2 → k) :=
  ⨅ l : List ℕ+, LinearMap.ker (Matrix.mulVecLin (wordDefect χ l))

theorem exchangeTransport_one_eq_one (χ : ℕ+ →* kˣ) :
    exchangeTransport χ 1 = (1 : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [exchangeTransport]

theorem wordDefect_pair (χ : ℕ+ →* kˣ) (m n : ℕ+) :
    wordDefect χ [m, n] = exchangeCurvature χ m n := by
  simp [wordDefect, wordTransport, exchangeCurvature]

/-- **Pairwise coherence controls every strict reassociation defect.** -/
theorem wordKernel_eq_coherentKernel (χ : ℕ+ →* kˣ) :
    wordKernel χ = coherentKernel χ := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [mem_coherentKernel_iff]
    intro m n
    have := Submodule.mem_iInf _ |>.1 hv [m, n]
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, wordDefect_pair] at this
    exact this
  · intro v hv
    rw [wordKernel, Submodule.mem_iInf]
    intro l
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, wordDefect, Matrix.sub_mulVec, sub_eq_zero]
    induction l with
    | nil => simp [wordTransport, exchangeTransport_one_eq_one]
    | cons a t ih =>
      rw [wordTransport, List.map_cons, List.prod_cons, ← wordTransport,
        ← Matrix.mulVec_mulVec, ih, coherentKernel_isRep hv, List.prod_cons]

/-! ## Factorization through a categorical realization -/

open CategoryTheory

/-- **A polarized family that factors through a categorical realization of the multiplication
monoid has trivial character.**  Functoriality forces the family to be a monoid representation. -/
theorem eq_one_of_factors {𝒰 : Type*} [Category 𝒰] {χ : ℕ+ →* kˣ}
    (F : SingleObj ℕ+ ⥤ 𝒰) (R : 𝒰 ⥤ SingleObj (Matrix (Fin 2) (Fin 2) k))
    (hR : ∀ n : ℕ+, R.map (F.map (SingleObj.toEnd ℕ+ n)) = exchangeTransport χ n) :
    χ = 1 := by
  refine (exchangeTransport_mul_iff χ).1 fun m n => ?_
  have hmn : SingleObj.toEnd ℕ+ (m * n) =
      SingleObj.toEnd ℕ+ n ≫ SingleObj.toEnd ℕ+ m := by
    rw [map_mul]
    rfl
  have hcomp : R.map (F.map (SingleObj.toEnd ℕ+ (m * n))) =
      R.map (F.map (SingleObj.toEnd ℕ+ n ≫ SingleObj.toEnd ℕ+ m)) := by rw [hmn]
  rw [F.map_comp, R.map_comp, hR (m * n), hR n, hR m] at hcomp
  exact hcomp.symm

end

end RHTower
