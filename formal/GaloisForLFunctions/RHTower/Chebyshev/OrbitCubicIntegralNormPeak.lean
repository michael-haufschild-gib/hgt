import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicNormForm

/-!
# Exact integral maximizers of the cubic norm triangle

The real centroid need not be integral. For every row sum, the integral norm
maximizers are exactly the triples whose coordinates differ by at most one.
A full unit loss in the integer sum of pair products already exceeds the
defect caused by rounding the centroid.
-/

namespace RHTower.OrbitCubic.NumberFieldTrace

/-- The three integer barycentric coordinates are as equal as possible. -/
def balanced (a b c : ℤ) : Prop :=
  a ≤ b+1 ∧ b ≤ a+1 ∧ b ≤ c+1 ∧ c ≤ b+1 ∧ a ≤ c+1 ∧ c ≤ a+1

private def total (a b c : ℤ) := arm a c+arm b a+arm c b
private def pairs (a b c : ℤ) := a*b+b*c+c*a

private theorem total_eq (a b c : ℤ) : total a b c = 3+(a+b+c)+pairs a b c := by
  unfold total arm pairs
  ring

private theorem spread_identity (a b c : ℤ) :
    2*((a+b+c)^2-3*pairs a b c) = (a-b)^2+(b-c)^2+(c-a)^2 := by unfold pairs; ring

private theorem big_spread (a b c : ℤ) (h : ¬ balanced a b c) :
    1 < (a+b+c)^2-3*pairs a b c := by
  by_contra! he
  have hi := spread_identity a b c
  have hsmall : (a-b)^2+(b-c)^2+(c-a)^2 ≤ 2 := by linarith only [he,hi]
  have small {x : ℤ} (hx : x^2 ≤ 2) : -1 ≤ x ∧ x ≤ 1 := by
    constructor
    · by_contra! hn
      have hh : 0 ≤ (-x-2)*(-x+2) := mul_nonneg (by omega) (by omega)
      nlinarith only [hx,hh]
    · by_contra! hn
      have hh : 0 ≤ (x-2)*(x+2) := mul_nonneg (by omega) (by omega)
      nlinarith only [hx,hh]
  have hab := small (show (a-b)^2 ≤ 2 by linarith only [hsmall,sq_nonneg (b-c),sq_nonneg (c-a)])
  have hbc := small (show (b-c)^2 ≤ 2 by linarith only [hsmall,sq_nonneg (a-b),sq_nonneg (c-a)])
  have hca := small (show (c-a)^2 ≤ 2 by linarith only [hsmall,sq_nonneg (a-b),sq_nonneg (b-c)])
  apply h
  unfold balanced
  omega

private theorem norm_bound (a b c : ℤ) : 3*triangleNorm a b c ≤ (total a b c)^2 := by
  unfold triangleNorm total
  nlinarith only [sq_nonneg (arm a c-arm b a),sq_nonneg (arm b a-arm c b),sq_nonneg (arm c b-arm a c)]

/-- Separating one coordinate by two already costs more than the rounding defect. -/
private theorem strict_loss {a b c A B C : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a+b+c=A+B+C) (href : (A+B+C)^2-3*pairs A B C ≤ 1)
    (hclose : (total A B C-1)^2 < 3*triangleNorm A B C) (hbad : ¬ balanced a b c) :
    triangleNorm a b c < triangleNorm A B C := by
  have sp := big_spread a b c hbad
  rw [hs] at sp
  have ht : total a b c ≤ total A B C-1 := by rw [total_eq,total_eq,hs]; omega
  have hp : 0 ≤ total a b c := by unfold total arm; positivity
  have hq := mul_self_le_mul_self hp ht
  nlinarith only [hq,norm_bound a b c,hclose]

/-- Peak at the nearest lattice points to the centroid for every congruence class. -/
theorem integer_norm_peak (a b c : ℕ) :
    let s := a+b+c
    let k : ℤ := (s/3 : ℕ)
    let M := if s%3=0 then triangleNorm k k k else if s%3=1 then triangleNorm (k+1) k k
      else triangleNorm k (k+1) (k+1)
    triangleNorm (a:ℤ) b c ≤ M ∧
      (triangleNorm (a:ℤ) b c = M ↔ balanced a b c) := by
  intro s k M
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hs (r : ℕ) (hr : s%3 = r) : (a:ℤ)+b+c = 3*k+r := by
    have hn : a+b+c = 3*(s/3)+r := by dsimp only [s] at *; omega
    exact_mod_cast hn
  have split (A B C : ℤ) (hm : M=triangleNorm A B C)
      (hS : (a:ℤ)+b+c=A+B+C)
      (hT : (A+B+C)^2-3*pairs A B C ≤ 1)
      (hnear : (total A B C-1)^2 < 3*triangleNorm A B C)
      (hgood : balanced a b c → (a=A ∧ b=B ∧ c=C) ∨
        ((a:ℤ)=B ∧ b=C ∧ c=A) ∨ ((a:ℤ)=C ∧ b=A ∧ c=B)) :
      triangleNorm (a:ℤ) b c ≤ M ∧ (triangleNorm (a:ℤ) b c = M ↔ balanced a b c) := by
    rw [hm]
    by_cases hb : balanced a b c
    · have eq : triangleNorm (a:ℤ) b c = triangleNorm A B C := by
        rcases hgood hb with h|h|h <;> rw [h.1,h.2.1,h.2.2] <;> unfold triangleNorm <;> ring
      exact ⟨eq.le,⟨fun _ => hb,fun _ => eq⟩⟩
    · have hl := strict_loss (Int.natCast_nonneg a) (Int.natCast_nonneg b)
        (Int.natCast_nonneg c) hS hT hnear hb
      exact ⟨hl.le,⟨fun he => (hl.ne he).elim,fun hh => (hb hh).elim⟩⟩
  have ranges : s%3=0 ∨ s%3=1 ∨ s%3=2 := by omega
  rcases ranges with h0 | h1 | h2
  · have he := hs 0 h0
    apply split k k k (by simp [M,h0]) (by omega)
    · unfold pairs; nlinarith only
    · unfold total triangleNorm arm; nlinarith only [hk,sq_nonneg k]
    · unfold balanced; omega
  · have he := hs 1 h1
    apply split (k+1) k k (by simp [M,h1]) (by omega)
    · unfold pairs; nlinarith only
    · unfold total triangleNorm arm; nlinarith only [hk,sq_nonneg k]
    · unfold balanced; omega
  · have he := hs 2 h2
    apply split k (k+1) (k+1) (by simp [M,h2]) (by omega)
    · unfold pairs; nlinarith only
    · unfold total triangleNorm arm; nlinarith only [hk,sq_nonneg k]
    · unfold balanced; omega

#print axioms integer_norm_peak
end RHTower.OrbitCubic.NumberFieldTrace
