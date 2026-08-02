import GaloisForLFunctions.HTGeometry.GammaShiftShape

/-!
# The datum of the shifted law, and the projective boundary of a tuple

A line function with a nonzero residue against a shifted shape has only one such residue: the
`Γ`-degree, the real argument exponent, the logarithm exponent and the constant are all determined.
Two different data would make one shape strictly dominate the other, and the corresponding ratio of
normalizations would have to be both zero and nonzero.

With uniqueness in hand a finite family of such functions has a projective boundary: dividing by a
member whose datum is dominant, every ratio converges — to the quotient of the two constants when
the data tie, and to zero otherwise.  This is eq. (6) of the shifted law, from the data alone.
-/

open Filter Set Topology Function Real

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {σ lam : ℝ}

/-- The shape is eventually nonzero on the line. -/
theorem eventually_gammaShiftShape_ne_zero (hσ : 0 < σ + lam) (d : ℤ) (ω : ℝ) (b : ℤ) :
    ∀ᶠ t : ℝ in atTop, gammaShiftShape lam σ d ω b t ≠ 0 := by
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  exact gammaShiftShape_ne_zero hσ ht d ω b

/-- A line function with a nonzero residue is eventually nonzero. -/
theorem eventually_ne_zero_of_shiftDatum {φ : ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ} (hc : c ≠ 0)
    (h : Tendsto (fun t : ℝ => φ t / gammaShiftShape lam σ d ω b t) atTop (nhds c)) :
    ∀ᶠ t : ℝ in atTop, φ t ≠ 0 := by
  filter_upwards [h.eventually (eventually_ne_nhds hc)] with t ht
  intro h0
  exact ht (by rw [h0, zero_div])

/-- Two shifted data are equal, or one of them dominates. -/
theorem shiftShape_trichotomy (d : ℤ) (ω : ℝ) (b : ℤ) (d' : ℤ) (ω' : ℝ) (b' : ℤ) :
    (d = d' ∧ ω = ω' ∧ b = b')
      ∨ ShiftShapeDominates d ω b d' ω' b'
      ∨ ShiftShapeDominates d' ω' b' d ω b := by
  rcases lt_trichotomy d d' with hd | hd | hd
  · exact Or.inr (Or.inl (Or.inl hd))
  · rcases lt_trichotomy ω ω' with hω | hω | hω
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd, hω⟩)))
    · rcases lt_trichotomy b b' with hb | hb | hb
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hd, hω, hb⟩)))
      · exact Or.inl ⟨hd, hω, hb⟩
      · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨hd.symm, hω.symm, hb⟩)))
    · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hd.symm, hω⟩)))
  · exact Or.inr (Or.inr (Or.inl hd))

/-- **The datum of a line function is unique.**  Against two different shifted shapes a function
cannot have two nonzero residues, and against one shape it has only one. -/
theorem shiftShape_datum_unique (hσ : 0 < σ + lam) {φ : ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ}
    {d' : ℤ} {ω' : ℝ} {b' : ℤ} {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : Tendsto (fun t : ℝ => φ t / gammaShiftShape lam σ d ω b t) atTop (nhds c))
    (h' : Tendsto (fun t : ℝ => φ t / gammaShiftShape lam σ d' ω' b' t) atTop (nhds c')) :
    d = d' ∧ ω = ω' ∧ b = b' ∧ c = c' := by
  classical
  have hratio : ∀ {p : ℤ} {q : ℝ} {r : ℤ} {p' : ℤ} {q' : ℝ} {r' : ℤ} {u v : ℂ}, v ≠ 0 →
      Tendsto (fun t : ℝ => φ t / gammaShiftShape lam σ p q r t) atTop (nhds u) →
      Tendsto (fun t : ℝ => φ t / gammaShiftShape lam σ p' q' r' t) atTop (nhds v) →
      Tendsto (fun t : ℝ => gammaShiftShape lam σ p' q' r' t / gammaShiftShape lam σ p q r t)
        atTop (nhds (u / v)) := by
    intro p q r p' q' r' u v hv hu hvlim
    refine (hu.div hvlim hv).congr' ?_
    filter_upwards [eventually_gammaShiftShape_ne_zero (σ := σ) hσ p q r,
      eventually_gammaShiftShape_ne_zero (σ := σ) hσ p' q' r',
      eventually_ne_zero_of_shiftDatum (σ := σ) hv hvlim] with t hS hS' hφ
    simp only [Pi.div_apply]
    field_simp
  have hfwd := hratio hc' h h'
  have hbwd := hratio hc h' h
  have hdata : d = d' ∧ ω = ω' ∧ b = b' := by
    rcases shiftShape_trichotomy d ω b d' ω' b' with heq | hsub | hsub'
    · exact heq
    · have hzero := tendsto_gammaShiftShape_ratio_zero (σ := σ) hσ hsub
      have := tendsto_nhds_unique hzero hfwd
      exact absurd this.symm (div_ne_zero hc hc')
    · have hzero := tendsto_gammaShiftShape_ratio_zero (σ := σ) hσ hsub'
      have := tendsto_nhds_unique hzero hbwd
      exact absurd this.symm (div_ne_zero hc' hc)
  obtain ⟨hd, hω, hb⟩ := hdata
  refine ⟨hd, hω, hb, ?_⟩
  subst hd; subst hω; subst hb
  exact tendsto_nhds_unique h h'

/-- **The projective boundary of a finite family, eq. (6).**  Dividing by a member with dominant
datum, every ratio converges: to the quotient of the constants when the data tie, and to zero
otherwise.  The dominant member's own ratio is `1`. -/
theorem exists_dominant_shiftShape_ratio (hσ : 0 < σ + lam) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hc : ∀ α, c α ≠ 0)
    (hlim : ∀ α, Tendsto
      (fun t : ℝ => F α t / gammaShiftShape lam σ (d α) (ω α) (b α) t) atTop (nhds (c α))) :
    ∃ (β : Fin N) (r : Fin N → ℂ), r β = 1 ∧
      ∀ α : Fin N, Tendsto (fun t : ℝ => F α t / F β t) atTop (nhds (r α)) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shiftShape_index hN d ω b
  have hinv : Tendsto
      (fun t : ℝ => (F β t / gammaShiftShape lam σ (d β) (ω β) (b β) t)⁻¹) atTop
      (nhds (c β)⁻¹) := (hlim β).inv₀ (hc β)
  refine ⟨β, fun α => if (d α = d β ∧ ω α = ω β ∧ b α = b β) then c α / c β else 0, ?_, ?_⟩
  · dsimp only
    rw [if_pos ⟨rfl, rfl, rfl⟩, div_self (hc β)]
  · intro α
    dsimp only
    rcases hβ α with ⟨hd, hω, hb⟩ | hsub
    · rw [if_pos ⟨hd, hω, hb⟩]
      have hmain := (hlim α).mul hinv
      rw [show c α * (c β)⁻¹ = c α / c β from (div_eq_mul_inv _ _).symm] at hmain
      refine hmain.congr' ?_
      filter_upwards [eventually_gammaShiftShape_ne_zero (σ := σ) hσ (d β) (ω β) (b β),
        eventually_ne_zero_of_shiftDatum (σ := σ) (hc β) (hlim β)] with t hS hFβ
      have hSα : gammaShiftShape lam σ (d α) (ω α) (b α) t
          = gammaShiftShape lam σ (d β) (ω β) (b β) t := by
        rw [hd, hω, hb]
      rw [hSα]
      field_simp
    · rw [if_neg (by
        rintro ⟨hd, hω, hb⟩
        rcases hsub with h | ⟨-, h⟩ | ⟨-, -, h⟩
        · omega
        · linarith
        · omega)]
      have hzero := tendsto_gammaShiftShape_ratio_zero (σ := σ) hσ hsub
      have hmain := ((hlim α).mul hzero).mul hinv
      rw [mul_zero, zero_mul] at hmain
      refine hmain.congr' ?_
      filter_upwards [eventually_gammaShiftShape_ne_zero (σ := σ) hσ (d α) (ω α) (b α),
        eventually_gammaShiftShape_ne_zero (σ := σ) hσ (d β) (ω β) (b β),
        eventually_ne_zero_of_shiftDatum (σ := σ) (hc β) (hlim β)] with t hSα hSβ hFβ
      field_simp

end

end GaloisForLFunctions.HTGeometry
