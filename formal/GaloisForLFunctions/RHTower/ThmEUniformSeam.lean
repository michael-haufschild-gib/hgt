import GaloisForLFunctions.RHTower.ThmEUniformTraceSquare
import GaloisForLFunctions.RHTower.DirichletLUniformRvM
import GaloisForLFunctions.RHTower.Zeta23FamilyBandwidth
import Zeta23.ThmE.Final

/-!
# The rank–trace seam for a primitive Dirichlet L-function at one height

For a primitive character `χ` modulo `q > 1`, the Alpöge–Furman certificate at a single height `T`
needs only:

* the block structure of the zero-side Gram matrix (Poisson summation, `8w ≤ L`),
* the tail inputs, here with the modulus-uniform local count `N_χ(t, t+1] ≤ A_u (1 + log q) log(|t| + 3)`,
* the bridge `G_z = G_p` (explicit formula for `L(s, χ)`),
* a trace bound `|tr G̃ − aLN| ≤ C₁ L √X`, a Frobenius bound `tr G̃² − M ≤ E·M`, and a lower
  Riemann–von Mangoldt bound `T ℓ_{1,q}/2π ≤ N + R_N`.

With these, `seam_at` gives

`H(λ_{1,q}) N − [4R₁ + R₂ + 3N_II + B(4 + 2√(c_λ N + R₂) + B)] ≤ N₀*(T, 2T)`

with `R₁ = C₁√X/a`, `R₂ = c_λ(((1+E)/a² − 1)N + (1+E)R_N/a²)`, `c_λ = 1/λ_{1,q} + λ_{1,q}/3`,
`B = θ₀/(aL)` and `θ₀ = 4A₀(e^{L/4}C₁')² log(4T)/T`, `A₀ = A_u(1 + log q)`.  Every input is stated at the
single height `T`, so the constants that enter are exactly those supplied; nothing depends on `q`
beyond what is displayed.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide Zeta23.Assembly RHLinalg

noncomputable section

namespace RHTower

/-- The parameters with the standard taper, bandwidth `λ` and ramp width `1`. -/
abbrev stdParams (lam : ℝ) : Params := paramsOf stdProfile lam

/-- The modulus-uniform local-count constant `A_u = 2(log 24 + 2)/log(0.95/0.84)`. -/
abbrev uniformA : ℝ := 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84)

/-- **The seam at one height.** -/
theorem seam_at {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ}
    (hT300 : Tail.T₀ ≤ T) (hwL : 8 * (stdParams lam).w ≤ (stdParams lam).L T)
    {C₁ ET RN : ℝ}
    (htr1 : |trGtildeChi (stdParams lam) (parity χ) q (coeff χ) T
        - (stdParams lam).a T * (stdParams lam).L T * (NcountL χ T (2 * T) : ℝ)|
        ≤ C₁ * ((stdParams lam).L T * Real.sqrt ((stdParams lam).X T)))
    (hET : 0 ≤ ET)
    (htr2 : trGtildeSqChi (stdParams lam) (parity χ) q (coeff χ) T - mainTr2Chi (stdParams lam) q T
        ≤ ET * mainTr2Chi (stdParams lam) q T)
    (hRvM : T * ell1q q T / (2 * π) ≤ (NcountL χ T (2 * T) : ℝ) + RN) :
    Hfun (lam1q (stdParams lam) q T) * (NcountL χ T (2 * T) : ℝ)
      - (4 * (C₁ * Real.sqrt ((stdParams lam).X T) / (stdParams lam).a T)
        + (1 / lam1q (stdParams lam) q T + lam1q (stdParams lam) q T / 3)
            * (((1 + 1 * ET) / (stdParams lam).a T ^ 2 - 1) * (NcountL χ T (2 * T) : ℝ)
              + (1 + 1 * ET) / (stdParams lam).a T ^ 2 * RN)
        + 3 * (NII (LZeros (LSeam_of hq hprim)) T : ℝ)
        + Tail.theta0 (uniformA * (1 + Real.log q))
              (Real.exp ((stdParams lam).L T / 4) * (stdParams lam).C1 T) T
            / ((stdParams lam).a T * (stdParams lam).L T)
          * (4 + 2 * Real.sqrt ((1 / lam1q (stdParams lam) q T + lam1q (stdParams lam) q T / 3)
                * (NcountL χ T (2 * T) : ℝ)
              + (1 / lam1q (stdParams lam) q T + lam1q (stdParams lam) q T / 3)
                * (((1 + 1 * ET) / (stdParams lam).a T ^ 2 - 1) * (NcountL χ T (2 * T) : ℝ)
                  + (1 + 1 * ET) / (stdParams lam).a T ^ 2 * RN))
            + Tail.theta0 (uniformA * (1 + Real.log q))
                (Real.exp ((stdParams lam).L T / 4) * (stdParams lam).C1 T) T
              / ((stdParams lam).a T * (stdParams lam).L T)))
      ≤ (N0starL χ T (2 * T) : ℝ) := by
  set P := stdParams lam with hPdef
  have hP : P.Valid := paramsOf_valid taperProfile_stdProfile h0 h1
  have hPfam : ParamsValidFam P := ⟨hP.taper, hP.lam_pos, hP.one_le_w⟩
  have hs : LSeam χ := LSeam_of hq hprim
  have hT0 : 0 < T := by have : (300:ℝ) ≤ T := hT300; linarith
  have hL8 : 8 ≤ P.L T := by have := hP.one_le_w; linarith
  have hL : 0 < P.L T := by linarith
  have ha2 : 1 / 2 ≤ P.a T := half_le_a_fam hPfam hwL
  have ha : 0 < P.a T := by linarith
  -- block and tail inputs
  have hBlock : BlockInputs (LZeros hs) P T :=
    ZeroSide.blockInputsAt (LZeros hs) P T (fun z => GzGp.phiHat_conj P T z)
      (fun r => GzGp.phiHat_ofReal P T r) (poissonSq_fam hPfam hwL) hL (by positivity)
  have hA₀ : (1 : ℝ) ≤ uniformA * (1 + Real.log q) := by
    have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
    exact one_le_mul_of_one_le_of_one_le one_le_uniformLocalCountConst (by linarith)
  have hloc : ∀ t : ℝ, ((LZeros hs).N t (t + 1) : ℝ)
      ≤ uniformA * (1 + Real.log q) * Real.log (|t| + 3) := by
    intro t; rw [LZeros_N]; exact uniform_localCount_log hq hprim t
  have hTail := tailInputs_fam (LZeros hs) hPfam hA₀ hloc hT300 (by linarith) hwL
  have hA := seamA hT0.le hBlock hTail ha hL
  -- the bridge and seam B
  have hEF := (paperInputsChi_L hq hprim).EF
  have hGzGp := GzGpChi_at P hP hEF T hL hwL
  have hl : 0 < l T := by
    have e : P.L T = lam * l T := rfl
    rw [e] at hL
    exact pos_of_mul_pos_right hL h0.le
  have hℓ₁ : 0 < ell1q q T := ell1q_pos hq.le hT0 hl
  have hN : ((LZeros hs).N T (2 * T) : ℝ) = (NcountL χ T (2 * T) : ℝ) := by rw [LZeros_N]
  rw [← hN] at htr1 hRvM
  have hSB := seamBChi P (parity χ) q (coeff χ) hGzGp ha hL hℓ₁ htr1 (C₂ := 1) (ET := ET)
    (by linarith) (by simpa using htr2) hRvM
  have hB₀ : 0 ≤ Tail.theta0 (uniformA * (1 + Real.log q))
      (Real.exp (P.L T / 4) * P.C1 T) T / (P.a T * P.L T) :=
    div_nonneg hTail.theta_nonneg (mul_pos ha hL).le
  have h := N0star_lower_H hB₀ hA hSB.1 hSB.2
  rw [LZeros_N0star, hN] at h
  exact h

end RHTower
