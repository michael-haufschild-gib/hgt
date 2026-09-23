import GaloisForLFunctions.RHTower.Sieve.BalancedPairsRescale
import GaloisForLFunctions.RHTower.Sieve.CoprimeSquarefreeDyadic

/-!
# The shared-prime sector density

Matomäki–Radziwiłł's theorem is uniform in the pair of parameters, so it applies at the rescaled
pair `(X_p, h_p) = (x/p², h/p)` as well as at `(x, h)`.  Recording that uniformity as
`MRBilinearAt f X hh` and instantiating at the weight `μ²·1_{p∤·}` gives the card's `(9)`:

    C_p(x,h) / (h√x log 2)  →  D²/(p+1)².

The factor `1/p²` is the Jacobian of the bijection `(m₁,m₂) ↦ (p m₁, p m₂)`, and
`(D·p/(p+1))²/p² = D²/(p+1)²`.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- **The bilinear all-interval theorem at a moving pair of parameters.** -/
def MRBilinearAt (f : ℕ → ℝ) (X hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => pairSum f (X x) (hh x) / (hh x * Real.sqrt (X x) * Real.log 2)
      - (blockMean f (X x)) ^ (2 : ℕ)) atTop (𝓝 0)

/-- The unrescaled interface is the moving one at the identity. -/
theorem MRBilinear_iff (f : ℕ → ℝ) (hh : ℝ → ℝ) :
    MRBilinear f hh ↔ MRBilinearAt f id hh := Iff.rfl

/-- The rescaled square root still grows. -/
theorem tendsto_sqrt_div_sq {p : ℕ} (hp : 0 < p) :
    Tendsto (fun x : ℝ => Real.sqrt (x / (p : ℝ) ^ (2 : ℕ))) atTop atTop := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hbase : Tendsto (fun x : ℝ => Real.sqrt x / (p : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.atTop_div_const hp0
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (sqrt_div_sq hx hp).symm

/-- **The rescaled block mean.**  Card equation `(8)` at the rescaled scale. -/
theorem tendsto_blockMean_coprime {p : ℕ} (hp : p.Prime) :
    Tendsto (fun x : ℝ => blockMean (coprimeSquarefreeWeight p) (x / (p : ℝ) ^ (2 : ℕ)))
      atTop (𝓝 (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))) := by
  have hbase := tendsto_window_coprime_squarefree_density hp
  exact hbase.comp (tendsto_sqrt_div_sq hp.pos)

/-- **Card equation (9).**  The shared-prime sector has density `D²/(p+1)²`. -/
theorem tendsto_sharedSector_of_MR {p : ℕ} (hp : p.Prime) {hh : ℝ → ℝ}
    (hMR : MRBilinearAt (coprimeSquarefreeWeight p)
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ))) :
    Tendsto (fun x => sharedSectorCount x (hh x) p / (hh x * Real.sqrt x * Real.log 2))
      atTop (𝓝 (squarefreeDensity ^ (2 : ℕ) / ((p : ℝ) + 1) ^ (2 : ℕ))) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
  have hmean := tendsto_blockMean_coprime hp
  have hsq : Tendsto (fun x : ℝ => (blockMean (coprimeSquarefreeWeight p) (x / (p : ℝ) ^ (2 : ℕ))) ^ (2 : ℕ))
      atTop (𝓝 ((squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) ^ (2 : ℕ))) := hmean.pow 2
  have hadd := hMR.add hsq
  rw [zero_add] at hadd
  have hraw : Tendsto (fun x : ℝ =>
      pairSum (coprimeSquarefreeWeight p) (x / (p : ℝ) ^ (2 : ℕ)) (hh x / (p : ℝ))
        / (hh x / (p : ℝ) * Real.sqrt (x / (p : ℝ) ^ (2 : ℕ)) * Real.log 2))
      atTop (𝓝 ((squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) ^ (2 : ℕ))) := by
    refine hadd.congr fun x => ?_
    ring
  have hscaled := hraw.const_mul (1 / (p : ℝ) ^ (2 : ℕ))
  have hconst : (1 / (p : ℝ) ^ (2 : ℕ)) * ((squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) ^ (2 : ℕ))
      = squarefreeDensity ^ (2 : ℕ) / ((p : ℝ) + 1) ^ (2 : ℕ) := by
    field_simp
  rw [hconst] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← sharedSectorCount_eq_pairSum hx hp, sqrt_div_sq hx.le hp.pos]
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  rw [show hh x / (p : ℝ) * (Real.sqrt x / (p : ℝ)) * Real.log 2
      = (hh x * Real.sqrt x * Real.log 2) / (p : ℝ) ^ (2 : ℕ) by ring]
  rw [div_div_eq_mul_div]
  field_simp

end RHTower.Sieve
