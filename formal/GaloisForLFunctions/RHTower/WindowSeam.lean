import GaloisForLFunctions.RHTower.WindowLadder
import GaloisForLFunctions.RHTower.SeamCongruence

/-!
# Height-window certificates from critical-line data

The weld between the finite-carrier line instruments and the height-window certificates.  The
sign-data instruments output, per ball window, the statement "every ξ-zero of this ball is on the
critical line (and simple)"; the certificate layer consumes exactly such balls
(`windowCertificate_of_ball_online_cover`).  Composed: a family of finite line certificates — EM
remainder bound, `emCarrier`/`gN` closeness, a LOW floor on the annulus charts, and a table of
certified ξ sign alternations on the line segment — covering the box window of height `T` forces
the height-`T` certificate at EVERY level, i.e. empties the box window of zeros.  At level `1`
this is the statement that line data forces `1 ≤ ladderHeight` at every box zero of the window;
at all levels jointly it is RH below height `T`.  Any other instrument producing on-line ball
covers plugs into the same consumer.
-/

namespace RHTower

open Complex Set Metric

/-- **The height-window certificate from finite line data.**  If every ξ-zero of the height-`T`
box window admits one LOW-floor EM sign certificate whose ball contains it — EM remainder bound
`ε₁`, `emCarrier`/`gN` closeness `δ`, LOW floor `ε₁ + δ` on the annulus charts, and `s` certified
ξ sign alternations on the line segment dominating the enclosed count — then the height-`T`
window certificate holds at every level `k`: the certified balls put every candidate zero on the
critical line, so the box window is empty and every divisibility clause is vacuous. -/
theorem windowCertificate_of_emCarrier_sign_certificates {k : ℕ} {T : ℝ}
    (hcert : ∀ ρ ∈ boxZeros T,
      ∃ N M : ℕ, ∃ t₁ t₂ : Finset ℂ, ∃ m₁ m₂ : ℂ → ℕ,
      ∃ H H' : ℂ → ℂ, ∃ a : ℂ, ∃ r₀ R ε₁ δ : ℝ, ∃ s : ℕ, ∃ ts : ℕ → ℝ,
        ρ ∈ ball a R ∧
        1 ≤ M ∧
        0 ≤ r₀ ∧ r₀ < R ∧
        (∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z) ∧
        (∀ z ∈ t₁, lineReflect z ∈ t₁) ∧
        (∀ w ∈ t₁, ‖w - a‖ ≤ r₀) ∧
        (∀ w ∈ t₂, ‖w - a‖ ≤ r₀) ∧
        AnalyticOnNhd ℂ H (ball a R) ∧
        (∀ z ∈ ball a R, H z ≠ 0) ∧
        AnalyticOnNhd ℂ H' (ball a R) ∧
        (∀ z ∈ ball a R, H' z ≠ 0) ∧
        (∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * H z) ∧
        (∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * H' z) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (ε₁ + δ) ∧
        (∀ i, i < s → ts i < ts (i + 1)) ∧
        (∀ i, i < s →
          (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0) ∧
        (∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R) ∧
        (∑ z ∈ t₂, m₂ z ≤ s)) :
    WindowCertificate k T := by
  refine windowCertificate_of_ball_online_cover ?_
  intro ρ hρ
  rcases hcert ρ hρ with
    ⟨N, M, t₁, t₂, m₁, m₂, H, H', a, r₀, R, ε₁, δ, s, ts,
      hρball, hM, h0, hrR, hm₁, hcl₁, hρ₁, hρ₂, hHan, hH0, hHpan, hHp0,
      hfact₁, hfact₂, hstripC, hE, hclose, hF, hmono, hsign, hseg, hcount₂⟩
  refine ⟨a, R, hρball, ?_⟩
  intro p hp hz
  exact (xi_window_simple_online_of_emCarrier_close_floor_sign_certificate
    (N := N) (M := M) hM h0 hrR hm₁ hcl₁ hρ₁ hρ₂ hHan hH0 hHpan hHp0
    hfact₁ hfact₂ hstripC hE hclose hF hmono hsign hseg hcount₂ p hp hz).1

/-- **Line data empties the window.**  The same family of finite line certificates forces the
certificate at every level at once, which is exactly the emptiness of the box window: RH below
height `T`, from finitely many finite-data checks. -/
theorem boxZeros_empty_of_emCarrier_sign_certificates {T : ℝ}
    (hcert : ∀ ρ ∈ boxZeros T,
      ∃ N M : ℕ, ∃ t₁ t₂ : Finset ℂ, ∃ m₁ m₂ : ℂ → ℕ,
      ∃ H H' : ℂ → ℂ, ∃ a : ℂ, ∃ r₀ R ε₁ δ : ℝ, ∃ s : ℕ, ∃ ts : ℕ → ℝ,
        ρ ∈ ball a R ∧
        1 ≤ M ∧
        0 ≤ r₀ ∧ r₀ < R ∧
        (∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z) ∧
        (∀ z ∈ t₁, lineReflect z ∈ t₁) ∧
        (∀ w ∈ t₁, ‖w - a‖ ≤ r₀) ∧
        (∀ w ∈ t₂, ‖w - a‖ ≤ r₀) ∧
        AnalyticOnNhd ℂ H (ball a R) ∧
        (∀ z ∈ ball a R, H z ≠ 0) ∧
        AnalyticOnNhd ℂ H' (ball a R) ∧
        (∀ z ∈ ball a R, H' z ≠ 0) ∧
        (∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * H z) ∧
        (∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * H' z) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (ε₁ + δ) ∧
        (∀ i, i < s → ts i < ts (i + 1)) ∧
        (∀ i, i < s →
          (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0) ∧
        (∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R) ∧
        (∑ z ∈ t₂, m₂ z ≤ s)) :
    boxZeros T = ∅ :=
  (forall_windowCertificate_iff_boxZeros_empty T).mp
    (fun _ => windowCertificate_of_emCarrier_sign_certificates hcert)

end RHTower
