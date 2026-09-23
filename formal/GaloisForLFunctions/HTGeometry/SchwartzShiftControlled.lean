import GaloisForLFunctions.HTGeometry.SchwartzOscillatorWord

/-!
# Operators controlled by a power of the shift

An operator on the Schwartz space is *controlled at order `m`* if applying any power of the shifted
number operator after it is bounded, in `L²`, by the corresponding power raised by `m`.  Words in
the oscillator operators are controlled at their length, and the class is closed under sums,
scalar multiples, composition — where the orders add — and raising the order.

Multiplication by the coordinate and differentiation are combinations of the two oscillator
operators, so both are controlled at order one, and every operator built from them is controlled at
the corresponding order; in particular the elliptic operator of the Sobolev estimate is controlled
at order two.

* `L2ShiftControlled` : the control predicate.
* `L2ShiftControlled.add`, `.smul`, `.comp`, `.mono` : the closure properties.
* `l2ShiftControlled_mulXCLM`, `_derivSCLM`, `_sobolevOp` : **the basic operators are
  controlled.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## Linearity of the iterated shift -/

theorem shiftedNumberCLM_iterate_add (j : ℕ) (u v : 𝓢(ℝ, ℂ)) :
    (shiftedNumberCLM^[j]) (u + v)
      = (shiftedNumberCLM^[j]) u + (shiftedNumberCLM^[j]) v := by
  induction j generalizing u v with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_add, ih]

theorem shiftedNumberCLM_iterate_smul (j : ℕ) (c : ℂ) (u : 𝓢(ℝ, ℂ)) :
    (shiftedNumberCLM^[j]) (c • u) = c • (shiftedNumberCLM^[j]) u := by
  induction j generalizing u with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_smul, ih]

theorem norm_toLp_iterate_le_succ (i : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ‖((shiftedNumberCLM^[i]) g).toLp 2 (volume : Measure ℝ)‖
      ≤ (4 * π)⁻¹ * ‖((shiftedNumberCLM^[i + 1]) g).toLp 2 (volume : Measure ℝ)‖ := by
  have h := norm_le_shiftedNumberCLM ((shiftedNumberCLM^[i]) g)
  have heq : (shiftedNumberCLM^[i + 1]) g = shiftedNumberCLM ((shiftedNumberCLM^[i]) g) :=
    Function.iterate_succ_apply' shiftedNumberCLM i g
  rw [heq]
  have hpi : (0 : ℝ) < 4 * π := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ hpi]
  linarith [h]

/-! ## The control predicate -/

/-- An operator is controlled at order `m` if a power of the shift applied after it is bounded by
the power raised by `m`. -/
def L2ShiftControlled (T : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) (m : ℕ) : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝓢(ℝ, ℂ),
    ‖((shiftedNumberCLM^[j]) (T g)).toLp 2 (volume : Measure ℝ)‖
      ≤ C * ‖((shiftedNumberCLM^[j + m]) g).toLp 2 (volume : Measure ℝ)‖

theorem l2ShiftControlled_oscWord (w : List Bool) :
    L2ShiftControlled (oscWord w) w.length :=
  fun j => oscWord_shift_bound w j

theorem l2ShiftControlled_id : L2ShiftControlled (fun g : 𝓢(ℝ, ℂ) => g) 0 := by
  intro j
  exact ⟨1, zero_le_one, fun g => by simp⟩

theorem L2ShiftControlled.mono {T : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)} {m : ℕ} (h : L2ShiftControlled T m) :
    L2ShiftControlled T (m + 1) := by
  intro j
  obtain ⟨C, hC, hbound⟩ := h j
  refine ⟨C * (4 * π)⁻¹, by positivity, fun g => ?_⟩
  have hstep := norm_toLp_iterate_le_succ (j + m) g
  have hjm : j + m + 1 = j + (m + 1) := by omega
  rw [hjm] at hstep
  calc ‖((shiftedNumberCLM^[j]) (T g)).toLp 2 (volume : Measure ℝ)‖
      ≤ C * ‖((shiftedNumberCLM^[j + m]) g).toLp 2 (volume : Measure ℝ)‖ := hbound g
    _ ≤ C * ((4 * π)⁻¹ * ‖((shiftedNumberCLM^[j + (m + 1)]) g).toLp
        2 (volume : Measure ℝ)‖) := mul_le_mul_of_nonneg_left hstep hC
    _ = C * (4 * π)⁻¹ * ‖((shiftedNumberCLM^[j + (m + 1)]) g).toLp
        2 (volume : Measure ℝ)‖ := by ring

theorem L2ShiftControlled.mono_le {T : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)} {m n : ℕ} (h : L2ShiftControlled T m)
    (hmn : m ≤ n) : L2ShiftControlled T n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => simpa using h
  | succ d ih =>
    have hd : m + (d + 1) = (m + d) + 1 := by omega
    rw [hd]
    exact ih.mono

theorem L2ShiftControlled.add {S T : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)} {m : ℕ} (hS : L2ShiftControlled S m)
    (hT : L2ShiftControlled T m) : L2ShiftControlled (fun g => S g + T g) m := by
  intro j
  obtain ⟨C₁, hC₁, h₁⟩ := hS j
  obtain ⟨C₂, hC₂, h₂⟩ := hT j
  refine ⟨C₁ + C₂, by positivity, fun g => ?_⟩
  calc ‖((shiftedNumberCLM^[j]) (S g + T g)).toLp 2 (volume : Measure ℝ)‖
      = ‖((shiftedNumberCLM^[j]) (S g) + (shiftedNumberCLM^[j]) (T g)).toLp
          2 (volume : Measure ℝ)‖ := by rw [shiftedNumberCLM_iterate_add]
    _ ≤ ‖((shiftedNumberCLM^[j]) (S g)).toLp 2 (volume : Measure ℝ)‖
        + ‖((shiftedNumberCLM^[j]) (T g)).toLp 2 (volume : Measure ℝ)‖ := by
        rw [toLp_add]
        exact norm_add_le _ _
    _ ≤ C₁ * ‖((shiftedNumberCLM^[j + m]) g).toLp 2 (volume : Measure ℝ)‖
        + C₂ * ‖((shiftedNumberCLM^[j + m]) g).toLp 2 (volume : Measure ℝ)‖ :=
        add_le_add (h₁ g) (h₂ g)
    _ = (C₁ + C₂) * ‖((shiftedNumberCLM^[j + m]) g).toLp 2 (volume : Measure ℝ)‖ := by ring

theorem L2ShiftControlled.smul {T : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)} {m : ℕ} (c : ℂ)
    (hT : L2ShiftControlled T m) : L2ShiftControlled (fun g => c • T g) m := by
  intro j
  obtain ⟨C, hC, hbound⟩ := hT j
  refine ⟨‖c‖ * C, by positivity, fun g => ?_⟩
  calc ‖((shiftedNumberCLM^[j]) (c • T g)).toLp 2 (volume : Measure ℝ)‖
      = ‖c‖ * ‖((shiftedNumberCLM^[j]) (T g)).toLp 2 (volume : Measure ℝ)‖ := by
        rw [shiftedNumberCLM_iterate_smul, toLp_smul, norm_smul]
    _ ≤ ‖c‖ * (C * ‖((shiftedNumberCLM^[j + m]) g).toLp 2 (volume : Measure ℝ)‖) :=
        mul_le_mul_of_nonneg_left (hbound g) (norm_nonneg c)
    _ = ‖c‖ * C * ‖((shiftedNumberCLM^[j + m]) g).toLp 2 (volume : Measure ℝ)‖ := by ring

theorem L2ShiftControlled.comp {S T : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)} {m n : ℕ} (hS : L2ShiftControlled S m)
    (hT : L2ShiftControlled T n) : L2ShiftControlled (fun g => S (T g)) (m + n) := by
  intro j
  obtain ⟨C₁, hC₁, h₁⟩ := hS j
  obtain ⟨C₂, hC₂, h₂⟩ := hT (j + m)
  refine ⟨C₁ * C₂, by positivity, fun g => ?_⟩
  have hassoc : j + m + n = j + (m + n) := by omega
  calc ‖((shiftedNumberCLM^[j]) (S (T g))).toLp 2 (volume : Measure ℝ)‖
      ≤ C₁ * ‖((shiftedNumberCLM^[j + m]) (T g)).toLp 2 (volume : Measure ℝ)‖ := h₁ (T g)
    _ ≤ C₁ * (C₂ * ‖((shiftedNumberCLM^[j + m + n]) g).toLp 2 (volume : Measure ℝ)‖) :=
        mul_le_mul_of_nonneg_left (h₂ g) hC₁
    _ = C₁ * C₂ * ‖((shiftedNumberCLM^[j + (m + n)]) g).toLp 2 (volume : Measure ℝ)‖ := by
        rw [hassoc]
        ring

theorem L2ShiftControlled.order_congr {T : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)} {m n : ℕ}
    (h : L2ShiftControlled T m) (hmn : m = n) : L2ShiftControlled T n := hmn ▸ h

theorem L2ShiftControlled.congr {S T : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)} {m : ℕ} (h : L2ShiftControlled S m)
    (hfun : ∀ g, S g = T g) : L2ShiftControlled T m := by
  intro j
  obtain ⟨C, hC, hbound⟩ := h j
  refine ⟨C, hC, fun g => ?_⟩
  rw [← hfun g]
  exact hbound g

/-! ## The basic operators are controlled -/

theorem l2ShiftControlled_creationCLM : L2ShiftControlled (fun g => creationCLM g) 1 := by
  have h := l2ShiftControlled_oscWord [true]
  have hfun : oscWord [true] = fun g : 𝓢(ℝ, ℂ) => creationCLM g := by
    funext g
    rw [oscWord_cons_true, oscWord_nil]
  have hlen : ([true] : List Bool).length = 1 := rfl
  rw [hfun, hlen] at h
  exact h

theorem l2ShiftControlled_annihilationCLM :
    L2ShiftControlled (fun g => annihilationCLM g) 1 := by
  have h := l2ShiftControlled_oscWord [false]
  have hfun : oscWord [false] = fun g : 𝓢(ℝ, ℂ) => annihilationCLM g := by
    funext g
    rw [oscWord_cons_false, oscWord_nil]
  have hlen : ([false] : List Bool).length = 1 := rfl
  rw [hfun, hlen] at h
  exact h

theorem l2ShiftControlled_mulXCLM : L2ShiftControlled (fun g => mulXCLM g) 1 := by
  have hsum : L2ShiftControlled (fun g : 𝓢(ℝ, ℂ) => creationCLM g + annihilationCLM g) 1 :=
    l2ShiftControlled_creationCLM.add l2ShiftControlled_annihilationCLM
  refine (hsum.smul ((4 * (π : ℂ))⁻¹)).congr fun g => ?_
  exact (mulXCLM_eq_oscillator g).symm

theorem l2ShiftControlled_derivSCLM : L2ShiftControlled (fun g => derivSCLM g) 1 := by
  have hneg : L2ShiftControlled (fun g : 𝓢(ℝ, ℂ) => annihilationCLM g + (-1 : ℂ) • creationCLM g)
      1 := l2ShiftControlled_annihilationCLM.add (l2ShiftControlled_creationCLM.smul (-1 : ℂ))
  refine (hneg.smul ((2 : ℂ)⁻¹)).congr fun g => ?_
  rw [derivSCLM_eq_oscillator g]
  congr 1
  rw [neg_one_smul]
  abel

theorem l2ShiftControlled_sobolevOp : L2ShiftControlled (fun g => sobolevOp g) 2 := by
  have hderiv2 : L2ShiftControlled (fun g : 𝓢(ℝ, ℂ) => derivSCLM (derivSCLM g)) 2 :=
    (l2ShiftControlled_derivSCLM.comp l2ShiftControlled_derivSCLM).order_congr
      (by norm_num : 1 + 1 = 2)
  have hid : L2ShiftControlled (fun g : 𝓢(ℝ, ℂ) => g) 2 :=
    l2ShiftControlled_id.mono_le (by norm_num)
  refine (hid.add (hderiv2.smul (-((4 * (π : ℂ) ^ (2 : ℕ))⁻¹)))).congr fun g => ?_
  rw [sobolevOp_apply, neg_smul, ← sub_eq_add_neg]

end GaloisForLFunctions

end
