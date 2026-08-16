import GaloisForLFunctions.HTGeometry.BruhatGroupUniqueness
import GaloisForLFunctions.HTGeometry.SteinbergTorusAction

/-!
# The Dennis–Stein addition relation in the second argument

Writing `x_ij(a) · x_ji(b₁) · x_ji(b₂)` in Bruhat form in two ways — once by merging the two
opposite generators first, once by decomposing them one at a time — gives

```text
⟨a, b₁⟩ · ⟨w₁⁻¹a, b₂⟩ · {W, w₁}⁻¹  =  ⟨a, b₁ + b₂⟩ ,
      w₁ = 1 + a b₁ ,   W = 1 + w₁⁻¹ a b₂ .
```

The two Bruhat words have *identical* outer parameters, not merely proportional ones, so the central
corrections cancel directly.  Checking that they are identical is the arithmetic heart: the opposite
parameters agree because `W b₁ + w₁⁻¹ b₂ = b₁ + b₂`, which is `w₁⁻¹ b₂ (1 + a b₁) = b₂`.

This is the first Dennis–Stein relation, in the `w`-parametrised form; the Steinberg symbol appears
explicitly as the price of merging the two torus factors.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The Dennis–Stein addition relation.** -/
theorem dennisStein_add_right {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b₁ b₂ : R) (w₁ W : Rˣ)
    (hw₁ : (w₁ : R) = 1 + a * b₁)
    (hW : (W : R) = 1 + (((w₁⁻¹ : Rˣ)) : R) * a * b₂) :
    dennisStein hij a b₁ w₁ * dennisStein hij ((((w₁⁻¹ : Rˣ)) : R) * a) b₂ W
        * (steinbergSymbol hij W w₁)⁻¹
      = dennisStein hij a (b₁ + b₂) (w₁ * W) := by
  have hc₁w : (((w₁⁻¹ : Rˣ)) : R) * (w₁ : R) = 1 := w₁.inv_mul
  have hCW : (((W⁻¹ : Rˣ)) : R) * (W : R) = 1 := W.inv_mul
  set c₁ : R := (((w₁⁻¹ : Rˣ)) : R) with hc₁def
  set C : R := (((W⁻¹ : Rˣ)) : R) with hCdef
  have hVinv : ((((w₁ * W)⁻¹ : Rˣ)) : R) = C * c₁ := by
    rw [hCdef, hc₁def, mul_inv]
    push_cast
    ring
  have hstep1 := steinbergX_mul_opposite hij a b₁ w₁
  have hstep2 := steinbergX_mul_opposite hij (c₁ * a) b₂ W
  have hway2 := steinbergX_mul_opposite hij a (b₁ + b₂) (w₁ * W)
  rw [← hc₁def] at hstep1
  rw [← hCdef] at hstep2
  have hD1c := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij a b₁ w₁ hw₁
    (Ne.symm hik) (Ne.symm hjk))
  have hD2c := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij (c₁ * a) b₂ W hW
    (Ne.symm hik) (Ne.symm hjk))
  have hmove := steinbergTorus_conj_transpose hij hik hjk w₁ (b₂ * C)
  rw [← hc₁def] at hmove
  have htor : steinbergTorus hij w₁ * steinbergX (Ne.symm hij) (b₂ * C)
      = steinbergX (Ne.symm hij) (c₁ * (b₂ * C) * c₁) * steinbergTorus hij w₁ := by
    rw [← hmove]
    group
  have hmerge : steinbergTorus hij w₁ * steinbergTorus hij W
      = (steinbergSymbol hij W w₁)⁻¹ * steinbergTorus hij (w₁ * W) := by
    have h := steinbergTorus_mul hij W w₁
    rw [mul_comm W w₁] at h
    rw [h]
    group
  have hway1 : steinbergX hij a * steinbergX (Ne.symm hij) (b₁ + b₂)
      = steinbergX (Ne.symm hij) (b₁ * c₁ + c₁ * (b₂ * C) * c₁)
        * (dennisStein hij a b₁ w₁ * dennisStein hij (c₁ * a) b₂ W
            * (steinbergSymbol hij W w₁)⁻¹)
        * steinbergTorus hij (w₁ * W) * steinbergX hij (C * (c₁ * a)) := by
    calc steinbergX hij a * steinbergX (Ne.symm hij) (b₁ + b₂)
        = steinbergX hij a * steinbergX (Ne.symm hij) b₁ * steinbergX (Ne.symm hij) b₂ := by
          rw [← steinbergX_mul (Ne.symm hij) b₁ b₂]
          group
      _ = steinbergX (Ne.symm hij) (b₁ * c₁)
            * (dennisStein hij a b₁ w₁ * steinbergTorus hij w₁)
            * (steinbergX hij (c₁ * a) * steinbergX (Ne.symm hij) b₂) := by
          rw [hstep1]
          group
      _ = steinbergX (Ne.symm hij) (b₁ * c₁)
            * (dennisStein hij a b₁ w₁ * steinbergTorus hij w₁)
            * (steinbergX (Ne.symm hij) (b₂ * C)
              * (dennisStein hij (c₁ * a) b₂ W * steinbergTorus hij W)
              * steinbergX hij (C * (c₁ * a))) := by rw [hstep2]
      _ = steinbergX (Ne.symm hij) (b₁ * c₁) * dennisStein hij a b₁ w₁
            * (steinbergTorus hij w₁ * steinbergX (Ne.symm hij) (b₂ * C))
            * (dennisStein hij (c₁ * a) b₂ W * steinbergTorus hij W)
            * steinbergX hij (C * (c₁ * a)) := by group
      _ = steinbergX (Ne.symm hij) (b₁ * c₁) * dennisStein hij a b₁ w₁
            * (steinbergX (Ne.symm hij) (c₁ * (b₂ * C) * c₁) * steinbergTorus hij w₁)
            * (dennisStein hij (c₁ * a) b₂ W * steinbergTorus hij W)
            * steinbergX hij (C * (c₁ * a)) := by rw [htor]
      _ = steinbergX (Ne.symm hij) (b₁ * c₁)
            * (dennisStein hij a b₁ w₁ * steinbergX (Ne.symm hij) (c₁ * (b₂ * C) * c₁))
            * steinbergTorus hij w₁
            * (dennisStein hij (c₁ * a) b₂ W * steinbergTorus hij W)
            * steinbergX hij (C * (c₁ * a)) := by group
      _ = steinbergX (Ne.symm hij) (b₁ * c₁)
            * (steinbergX (Ne.symm hij) (c₁ * (b₂ * C) * c₁) * dennisStein hij a b₁ w₁)
            * steinbergTorus hij w₁
            * (dennisStein hij (c₁ * a) b₂ W * steinbergTorus hij W)
            * steinbergX hij (C * (c₁ * a)) := by
          rw [← hD1c (steinbergX (Ne.symm hij) (c₁ * (b₂ * C) * c₁))]
      _ = steinbergX (Ne.symm hij) (b₁ * c₁)
            * steinbergX (Ne.symm hij) (c₁ * (b₂ * C) * c₁)
            * dennisStein hij a b₁ w₁
            * (steinbergTorus hij w₁ * dennisStein hij (c₁ * a) b₂ W)
            * steinbergTorus hij W
            * steinbergX hij (C * (c₁ * a)) := by group
      _ = steinbergX (Ne.symm hij) (b₁ * c₁)
            * steinbergX (Ne.symm hij) (c₁ * (b₂ * C) * c₁)
            * dennisStein hij a b₁ w₁
            * (dennisStein hij (c₁ * a) b₂ W * steinbergTorus hij w₁)
            * steinbergTorus hij W
            * steinbergX hij (C * (c₁ * a)) := by
          rw [hD2c (steinbergTorus hij w₁)]
      _ = steinbergX (Ne.symm hij) (b₁ * c₁)
            * steinbergX (Ne.symm hij) (c₁ * (b₂ * C) * c₁)
            * (dennisStein hij a b₁ w₁ * dennisStein hij (c₁ * a) b₂ W)
            * (steinbergTorus hij w₁ * steinbergTorus hij W)
            * steinbergX hij (C * (c₁ * a)) := by group
      _ = steinbergX (Ne.symm hij) (b₁ * c₁ + c₁ * (b₂ * C) * c₁)
            * (dennisStein hij a b₁ w₁ * dennisStein hij (c₁ * a) b₂ W
              * (steinbergSymbol hij W w₁)⁻¹)
            * steinbergTorus hij (w₁ * W) * steinbergX hij (C * (c₁ * a)) := by
          rw [steinbergX_mul, hmerge]
          group
  have hα : C * (c₁ * a) = ((((w₁ * W)⁻¹ : Rˣ)) : R) * a := by
    rw [hVinv]; ring
  have hβ : b₁ * c₁ + c₁ * (b₂ * C) * c₁ = (b₁ + b₂) * ((((w₁ * W)⁻¹ : Rˣ)) : R) := by
    rw [hVinv]
    have hmul : (b₁ * c₁ + c₁ * (b₂ * C) * c₁) * (W : R)
        = ((b₁ + b₂) * (C * c₁)) * (W : R) := by
      have e1 : c₁ * (b₂ * C) * c₁ * (W : R) = c₁ * c₁ * b₂ := by
        calc c₁ * (b₂ * C) * c₁ * (W : R) = c₁ * c₁ * b₂ * (C * (W : R)) := by ring
          _ = c₁ * c₁ * b₂ := by rw [hCW, mul_one]
      have e2 : ((b₁ + b₂) * (C * c₁)) * (W : R) = (b₁ + b₂) * c₁ := by
        calc ((b₁ + b₂) * (C * c₁)) * (W : R) = (b₁ + b₂) * c₁ * (C * (W : R)) := by ring
          _ = (b₁ + b₂) * c₁ := by rw [hCW, mul_one]
      rw [add_mul, e1, e2, hW]
      linear_combination (c₁ * b₂) * hc₁w - (c₁ * c₁ * b₂) * hw₁
    have hWC : (W : R) * C = 1 := by rw [mul_comm]; exact hCW
    have hcancel : (b₁ * c₁ + c₁ * (b₂ * C) * c₁) * (W : R) * C
        = ((b₁ + b₂) * (C * c₁)) * (W : R) * C := by rw [hmul]
    calc b₁ * c₁ + c₁ * (b₂ * C) * c₁
        = (b₁ * c₁ + c₁ * (b₂ * C) * c₁) * ((W : R) * C) := by rw [hWC, mul_one]
      _ = (b₁ * c₁ + c₁ * (b₂ * C) * c₁) * (W : R) * C := by ring
      _ = ((b₁ + b₂) * (C * c₁)) * (W : R) * C := hcancel
      _ = ((b₁ + b₂) * (C * c₁)) * ((W : R) * C) := by ring
      _ = (b₁ + b₂) * (C * c₁) := by rw [hWC, mul_one]
  have hway1' : steinbergX hij a * steinbergX (Ne.symm hij) (b₁ + b₂)
      = steinbergX (Ne.symm hij) ((b₁ + b₂) * ((((w₁ * W)⁻¹ : Rˣ)) : R))
        * (dennisStein hij a b₁ w₁ * dennisStein hij (c₁ * a) b₂ W
            * (steinbergSymbol hij W w₁)⁻¹)
        * steinbergTorus hij (w₁ * W)
        * steinbergX hij (((((w₁ * W)⁻¹ : Rˣ)) : R) * a) := by
    rw [hway1, hβ, hα]
  have hway2' : steinbergX hij a * steinbergX (Ne.symm hij) (b₁ + b₂)
      = steinbergX (Ne.symm hij) ((b₁ + b₂) * ((((w₁ * W)⁻¹ : Rˣ)) : R))
        * dennisStein hij a (b₁ + b₂) (w₁ * W)
        * steinbergTorus hij (w₁ * W)
        * steinbergX hij (((((w₁ * W)⁻¹ : Rˣ)) : R) * a) := by
    rw [hway2]
    group
  exact bruhat_center_unique hij (hway1'.symm.trans hway2')

end GaloisForLFunctions.HTGeometry

end
