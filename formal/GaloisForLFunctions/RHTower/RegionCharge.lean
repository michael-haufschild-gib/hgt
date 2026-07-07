/-
The quadrant-local deck charge and its transport under the functional-equation symmetries.

The deck charge of a finite zero configuration splits by region: `regionCharge n S ord R` is the
charge of the zeros of `S` lying in a region `R` (their total order, reduced mod `n`).  A region and
its complement partition the total charge (`regionCharge_add_compl`), and an order-preserving
involution that swaps two regions makes their charges equal (`regionCharge_transport`).

For the functional-equation Klein four-group `{s, 1−s, s̄, 1−s̄}` acting on an off-line zero set,
each of `s ↦ 1−s` (reflection across the critical line, negating the imaginary part) and `s ↦ s̄`
(conjugation) is an order-preserving involution; together they transport the four quadrant charges
into one another, so all four are equal and the *total* charge is `4·q` — invisible to the rung-`2`
(mod `4`) detector, while the single-quadrant charge `q` is the genuine signal.  This is the exact
sense in which globally symmetric charge counts are too coarse and the detector must be
quadrant-local.
-/
import GaloisForLFunctions.RHTower.DeckChargeCalculus

open Complex
open scoped Classical

namespace RHTower

/-- The rung-`n` deck charge of the zeros of `S` lying in a region `R`: the reduction of their total
order.  The quadrant-local refinement of the global charge. -/
noncomputable def regionCharge (n : ℕ) (S : Finset ℂ) (ord : ℂ → ℕ) (R : ℂ → Prop) : ZMod n :=
  wCharge n ((∑ ρ ∈ S.filter R, ord ρ : ℕ) : ℤ)

/-- **A region and its complement partition the total charge.** -/
theorem regionCharge_add_compl (n : ℕ) (S : Finset ℂ) (ord : ℂ → ℕ) (R : ℂ → Prop) :
    regionCharge n S ord R + regionCharge n S ord (fun ρ => ¬ R ρ)
      = wCharge n ((∑ ρ ∈ S, ord ρ : ℕ) : ℤ) := by
  rw [regionCharge, regionCharge, ← wCharge_add, ← Nat.cast_add]
  congr 2
  convert Finset.sum_filter_add_sum_filter_not S R ord using 2
  congr

/-- **Transport of quadrant charge.**  An involution `σ` that carries the `R₁`-zeros of `S` onto its
`R₂`-zeros (and back), preserving order, makes the two region charges equal: the functional-equation
symmetries move charge between quadrants without creating or destroying it. -/
theorem regionCharge_transport (n : ℕ) (S : Finset ℂ) (ord : ℂ → ℕ) (R₁ R₂ : ℂ → Prop) (σ : ℂ → ℂ)
    (hσ12 : ∀ ρ ∈ S, R₁ ρ → (σ ρ ∈ S ∧ R₂ (σ ρ)))
    (hσ21 : ∀ ρ ∈ S, R₂ ρ → (σ ρ ∈ S ∧ R₁ (σ ρ)))
    (hσσ : ∀ ρ ∈ S, σ (σ ρ) = ρ) (hord : ∀ ρ ∈ S, ord (σ ρ) = ord ρ) :
    regionCharge n S ord R₁ = regionCharge n S ord R₂ := by
  rw [regionCharge, regionCharge]
  congr 2
  apply Finset.sum_nbij' (i := σ) (j := σ)
  · intro a ha; rw [Finset.mem_filter] at ha ⊢; exact hσ12 a ha.1 ha.2
  · intro a ha; rw [Finset.mem_filter] at ha ⊢; exact hσ21 a ha.1 ha.2
  · intro a ha; rw [Finset.mem_filter] at ha; exact hσσ a ha.1
  · intro a ha; rw [Finset.mem_filter] at ha; exact hσσ a ha.1
  · intro a ha; rw [Finset.mem_filter] at ha; exact (hord a ha.1).symm

/-- **The four quadrant charges are equal.**  If two order-preserving involutions `σ`, `τ` of the
zero set `S` transport a region `R` to `R'`, `R''` and their composite to `R'''` respectively (the
functional-equation Klein four-group `{s, 1−s, s̄, 1−s̄}` on the four quadrants), then the four
quadrant charges coincide.  Consequently the total charge over the four is `4·q` and the mod-`4`
(rung-`2`) reading is blind, while `q` — the single-quadrant charge — carries the information. -/
theorem regionCharge_klein_equal (n : ℕ) (S : Finset ℂ) (ord : ℂ → ℕ)
    (R R' R'' R''' : ℂ → Prop) (σ τ : ℂ → ℂ)
    (hσσ : ∀ ρ ∈ S, σ (σ ρ) = ρ) (hσord : ∀ ρ ∈ S, ord (σ ρ) = ord ρ)
    (hσRR' : ∀ ρ ∈ S, R ρ → (σ ρ ∈ S ∧ R' (σ ρ))) (hσR'R : ∀ ρ ∈ S, R' ρ → (σ ρ ∈ S ∧ R (σ ρ)))
    (hττ : ∀ ρ ∈ S, τ (τ ρ) = ρ) (hτord : ∀ ρ ∈ S, ord (τ ρ) = ord ρ)
    (hτRR'' : ∀ ρ ∈ S, R ρ → (τ ρ ∈ S ∧ R'' (τ ρ))) (hτR''R : ∀ ρ ∈ S, R'' ρ → (τ ρ ∈ S ∧ R (τ ρ)))
    (hστRR''' : ∀ ρ ∈ S, R ρ → (σ (τ ρ) ∈ S ∧ R''' (σ (τ ρ))))
    (hστR'''R : ∀ ρ ∈ S, R''' ρ → (σ (τ ρ) ∈ S ∧ R (σ (τ ρ))))
    (hστστ : ∀ ρ ∈ S, σ (τ (σ (τ ρ))) = ρ) (hστord : ∀ ρ ∈ S, ord (σ (τ ρ)) = ord ρ) :
    regionCharge n S ord R = regionCharge n S ord R' ∧
    regionCharge n S ord R = regionCharge n S ord R'' ∧
    regionCharge n S ord R = regionCharge n S ord R''' := by
  refine ⟨regionCharge_transport n S ord R R' σ hσRR' hσR'R hσσ hσord,
    regionCharge_transport n S ord R R'' τ hτRR'' hτR''R hττ hτord,
    regionCharge_transport n S ord R R''' (fun ρ => σ (τ ρ)) hστRR''' hστR'''R hστστ hστord⟩

end RHTower
