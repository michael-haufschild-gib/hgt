import GaloisForLFunctions.HTGeometry.DennisSteinInverse

/-!
# The Dennis–Stein addition relation in the first argument

The mirror of the addition relation: decomposing `x_ij(a₁) · x_ij(a₂) · x_ji(b)` either by merging
the two diagonal generators first, or one Bruhat step at a time, gives

```text
⟨a₁, b w₂⁻¹⟩ · ⟨a₂, b⟩ · {w₂, U}⁻¹  =  ⟨a₁ + a₂, b⟩ ,
      w₂ = 1 + a₂ b ,   U = 1 + a₁ b w₂⁻¹ ,   U w₂ = 1 + (a₁ + a₂) b .
```

Again the outer Bruhat parameters of the two words coincide exactly.  The diagonal parameter needs
the identity `w₂⁻¹ a₁ + a₂ U = a₁ + a₂`, which reduces to `w₂⁻¹ a₁ (1 + a₂ b) = a₁`.

Together with the relation in the second argument this is the additive half of the Dennis–Stein
presentation: both arguments of `⟨·,·⟩` are additive up to a torus symbol and a rescaling of the
other argument.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The Dennis–Stein addition relation in the first argument.** -/
theorem dennisStein_add_left {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a₁ a₂ b : R) (w₂ U : Rˣ)
    (hw₂ : (w₂ : R) = 1 + a₂ * b)
    (hU : (U : R) = 1 + a₁ * (b * (((w₂⁻¹ : Rˣ)) : R))) :
    dennisStein hij a₁ (b * (((w₂⁻¹ : Rˣ)) : R)) U * dennisStein hij a₂ b w₂
        * (steinbergSymbol hij w₂ U)⁻¹
      = dennisStein hij (a₁ + a₂) b (U * w₂) := by
  have hc₂w : (((w₂⁻¹ : Rˣ)) : R) * (w₂ : R) = 1 := w₂.inv_mul
  have huU : (((U⁻¹ : Rˣ)) : R) * (U : R) = 1 := U.inv_mul
  set c₂ : R := (((w₂⁻¹ : Rˣ)) : R) with hc₂def
  set u : R := (((U⁻¹ : Rˣ)) : R) with hudef
  have hVinv : ((((U * w₂)⁻¹ : Rˣ)) : R) = c₂ * u := by
    rw [hc₂def, hudef, mul_inv]
    push_cast
    ring
  have hstep2 := steinbergX_mul_opposite hij a₂ b w₂
  have hstep1 := steinbergX_mul_opposite hij a₁ (b * c₂) U
  have hway2 := steinbergX_mul_opposite hij (a₁ + a₂) b (U * w₂)
  rw [← hc₂def] at hstep2
  rw [← hudef] at hstep1
  have hD1c := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij a₁ (b * c₂) U hU
    (Ne.symm hik) (Ne.symm hjk))
  have hD2c := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij a₂ b w₂ hw₂
    (Ne.symm hik) (Ne.symm hjk))
  have hmoveX : steinbergX hij (u * a₁) * steinbergTorus hij w₂
      = steinbergTorus hij w₂ * steinbergX hij (c₂ * (u * a₁) * c₂) := by
    have h := steinbergTorus_conj_self hij hik hjk w₂ (c₂ * (u * a₁) * c₂)
    have hval : (w₂ : R) * (c₂ * (u * a₁) * c₂) * (w₂ : R) = u * a₁ := by
      linear_combination (u * a₁ * (c₂ * (w₂ : R) + 1)) * hc₂w
    rw [hval] at h
    rw [← h]
    group
  have hmerge : steinbergTorus hij U * steinbergTorus hij w₂
      = (steinbergSymbol hij w₂ U)⁻¹ * steinbergTorus hij (U * w₂) := by
    have h := steinbergTorus_mul hij w₂ U
    rw [mul_comm w₂ U] at h
    rw [h]
    group
  have hway1 : steinbergX hij (a₁ + a₂) * steinbergX (Ne.symm hij) b
      = steinbergX (Ne.symm hij) (b * c₂ * u)
        * (dennisStein hij a₁ (b * c₂) U * dennisStein hij a₂ b w₂
            * (steinbergSymbol hij w₂ U)⁻¹)
        * steinbergTorus hij (U * w₂)
        * steinbergX hij (c₂ * (u * a₁) * c₂ + c₂ * a₂) := by
    calc steinbergX hij (a₁ + a₂) * steinbergX (Ne.symm hij) b
        = steinbergX hij a₁ * (steinbergX hij a₂ * steinbergX (Ne.symm hij) b) := by
          rw [← steinbergX_mul hij a₁ a₂]
          group
      _ = steinbergX hij a₁ * (steinbergX (Ne.symm hij) (b * c₂)
            * (dennisStein hij a₂ b w₂ * steinbergTorus hij w₂)
            * steinbergX hij (c₂ * a₂)) := by rw [hstep2]
      _ = steinbergX hij a₁ * steinbergX (Ne.symm hij) (b * c₂)
            * (dennisStein hij a₂ b w₂ * steinbergTorus hij w₂)
            * steinbergX hij (c₂ * a₂) := by group
      _ = steinbergX (Ne.symm hij) (b * c₂ * u)
            * (dennisStein hij a₁ (b * c₂) U * steinbergTorus hij U)
            * steinbergX hij (u * a₁)
            * (dennisStein hij a₂ b w₂ * steinbergTorus hij w₂)
            * steinbergX hij (c₂ * a₂) := by rw [hstep1]
      _ = steinbergX (Ne.symm hij) (b * c₂ * u) * dennisStein hij a₁ (b * c₂) U
            * steinbergTorus hij U
            * (steinbergX hij (u * a₁) * dennisStein hij a₂ b w₂)
            * steinbergTorus hij w₂ * steinbergX hij (c₂ * a₂) := by group
      _ = steinbergX (Ne.symm hij) (b * c₂ * u) * dennisStein hij a₁ (b * c₂) U
            * steinbergTorus hij U
            * (dennisStein hij a₂ b w₂ * steinbergX hij (u * a₁))
            * steinbergTorus hij w₂ * steinbergX hij (c₂ * a₂) := by
          rw [hD2c (steinbergX hij (u * a₁))]
      _ = steinbergX (Ne.symm hij) (b * c₂ * u) * dennisStein hij a₁ (b * c₂) U
            * (steinbergTorus hij U * dennisStein hij a₂ b w₂)
            * steinbergX hij (u * a₁)
            * steinbergTorus hij w₂ * steinbergX hij (c₂ * a₂) := by group
      _ = steinbergX (Ne.symm hij) (b * c₂ * u) * dennisStein hij a₁ (b * c₂) U
            * (dennisStein hij a₂ b w₂ * steinbergTorus hij U)
            * steinbergX hij (u * a₁)
            * steinbergTorus hij w₂ * steinbergX hij (c₂ * a₂) := by
          rw [hD2c (steinbergTorus hij U)]
      _ = steinbergX (Ne.symm hij) (b * c₂ * u)
            * (dennisStein hij a₁ (b * c₂) U * dennisStein hij a₂ b w₂)
            * steinbergTorus hij U
            * (steinbergX hij (u * a₁) * steinbergTorus hij w₂)
            * steinbergX hij (c₂ * a₂) := by group
      _ = steinbergX (Ne.symm hij) (b * c₂ * u)
            * (dennisStein hij a₁ (b * c₂) U * dennisStein hij a₂ b w₂)
            * steinbergTorus hij U
            * (steinbergTorus hij w₂ * steinbergX hij (c₂ * (u * a₁) * c₂))
            * steinbergX hij (c₂ * a₂) := by rw [hmoveX]
      _ = steinbergX (Ne.symm hij) (b * c₂ * u)
            * (dennisStein hij a₁ (b * c₂) U * dennisStein hij a₂ b w₂)
            * (steinbergTorus hij U * steinbergTorus hij w₂)
            * (steinbergX hij (c₂ * (u * a₁) * c₂) * steinbergX hij (c₂ * a₂)) := by group
      _ = steinbergX (Ne.symm hij) (b * c₂ * u)
            * (dennisStein hij a₁ (b * c₂) U * dennisStein hij a₂ b w₂
                * (steinbergSymbol hij w₂ U)⁻¹)
            * steinbergTorus hij (U * w₂)
            * steinbergX hij (c₂ * (u * a₁) * c₂ + c₂ * a₂) := by
          rw [hmerge, steinbergX_mul]
          group
  have hβ : b * c₂ * u = b * ((((U * w₂)⁻¹ : Rˣ)) : R) := by
    rw [hVinv]; ring
  have hα : c₂ * (u * a₁) * c₂ + c₂ * a₂
      = ((((U * w₂)⁻¹ : Rˣ)) : R) * (a₁ + a₂) := by
    rw [hVinv]
    have hUW : ((U : R) * (w₂ : R)) * (c₂ * u) = 1 := by
      calc ((U : R) * (w₂ : R)) * (c₂ * u)
          = (u * (U : R)) * (c₂ * (w₂ : R)) := by ring
        _ = 1 := by rw [huU, hc₂w, mul_one]
    have hmul : (c₂ * (u * a₁) * c₂ + c₂ * a₂) * ((U : R) * (w₂ : R))
        = ((c₂ * u) * (a₁ + a₂)) * ((U : R) * (w₂ : R)) := by
      have e1 : (c₂ * (u * a₁) * c₂ + c₂ * a₂) * ((U : R) * (w₂ : R))
          = c₂ * a₁ + a₂ * (U : R) := by
        calc (c₂ * (u * a₁) * c₂ + c₂ * a₂) * ((U : R) * (w₂ : R))
            = c₂ * a₁ * (u * (U : R)) * (c₂ * (w₂ : R))
              + a₂ * (U : R) * (c₂ * (w₂ : R)) := by ring
          _ = c₂ * a₁ + a₂ * (U : R) := by rw [huU, hc₂w]; ring
      have e2 : ((c₂ * u) * (a₁ + a₂)) * ((U : R) * (w₂ : R)) = a₁ + a₂ := by
        calc ((c₂ * u) * (a₁ + a₂)) * ((U : R) * (w₂ : R))
            = (a₁ + a₂) * (u * (U : R)) * (c₂ * (w₂ : R)) := by ring
          _ = a₁ + a₂ := by rw [huU, hc₂w]; ring
      rw [e1, e2, hU]
      linear_combination a₁ * hc₂w - (a₁ * c₂) * hw₂
    calc c₂ * (u * a₁) * c₂ + c₂ * a₂
        = (c₂ * (u * a₁) * c₂ + c₂ * a₂) * (((U : R) * (w₂ : R)) * (c₂ * u)) := by
          rw [hUW, mul_one]
      _ = ((c₂ * (u * a₁) * c₂ + c₂ * a₂) * ((U : R) * (w₂ : R))) * (c₂ * u) := by ring
      _ = (((c₂ * u) * (a₁ + a₂)) * ((U : R) * (w₂ : R))) * (c₂ * u) := by rw [hmul]
      _ = ((c₂ * u) * (a₁ + a₂)) * (((U : R) * (w₂ : R)) * (c₂ * u)) := by ring
      _ = (c₂ * u) * (a₁ + a₂) := by rw [hUW, mul_one]
  have hway1' : steinbergX hij (a₁ + a₂) * steinbergX (Ne.symm hij) b
      = steinbergX (Ne.symm hij) (b * ((((U * w₂)⁻¹ : Rˣ)) : R))
        * (dennisStein hij a₁ (b * c₂) U * dennisStein hij a₂ b w₂
            * (steinbergSymbol hij w₂ U)⁻¹)
        * steinbergTorus hij (U * w₂)
        * steinbergX hij (((((U * w₂)⁻¹ : Rˣ)) : R) * (a₁ + a₂)) := by
    rw [hway1, hβ, hα]
  have hway2' : steinbergX hij (a₁ + a₂) * steinbergX (Ne.symm hij) b
      = steinbergX (Ne.symm hij) (b * ((((U * w₂)⁻¹ : Rˣ)) : R))
        * dennisStein hij (a₁ + a₂) b (U * w₂)
        * steinbergTorus hij (U * w₂)
        * steinbergX hij (((((U * w₂)⁻¹ : Rˣ)) : R) * (a₁ + a₂)) := by
    rw [hway2]
    group
  exact bruhat_center_unique hij (hway1'.symm.trans hway2')

end GaloisForLFunctions.HTGeometry

end
