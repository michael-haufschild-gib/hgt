import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.RealRe
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.RealIm
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryLowCore77 (h s : ℝ) : ℝ :=
  (((((h^(6-6:ℕ) * (s ^ 1 * (104096251904/531441 : ℝ))) + (h^(6-6:ℕ) * (s ^ 2 * (336723968/6561 : ℝ)))) + ((h^(6-6:ℕ) * (s ^ 3 * (-1301807104/531441 : ℝ))) + (h^(7-6:ℕ) * (s ^ 1 * (-1304204238848/4782969 : ℝ))))) + (((h^(7-6:ℕ) * (s ^ 2 * (-47163277312/1594323 : ℝ))) + (h^(7-6:ℕ) * (s ^ 3 * (1592262656/1594323 : ℝ)))) + ((h^(8-6:ℕ) * (s ^ 2 * (-23604740096/4782969 : ℝ))) + ((h^(8-6:ℕ) * (s ^ 3 * (-3967516672/1594323 : ℝ))) + (h^(8-6:ℕ) * (s ^ 4 * (692584448/1594323 : ℝ))))))) + ((((h^(9-6:ℕ) * (s ^ 3 * (40742912000/4782969 : ℝ))) + (h^(9-6:ℕ) * (s ^ 4 * (-4044161024/4782969 : ℝ)))) + ((h^(10-6:ℕ) * (s ^ 3 * (-51636723712/14348907 : ℝ))) + (h^(10-6:ℕ) * (s ^ 4 * (2856648704/14348907 : ℝ))))) + (((h^(10-6:ℕ) * (s ^ 5 * (-92569600/4782969 : ℝ))) + (h^(11-6:ℕ) * (s ^ 4 * (1094238208/4782969 : ℝ)))) + ((h^(11-6:ℕ) * (s ^ 5 * (323993600/4782969 : ℝ))) + ((h^(12-6:ℕ) * (s ^ 5 * (-1133977600/14348907 : ℝ))) + (h^(13-6:ℕ) * (s ^ 5 * (3968921600/129140163 : ℝ))))))))

theorem boundaryLowCore77_ofReal (h s : ℝ) :
    ((boundaryLowCore77 h s:ℝ):ℂ)=boundaryLowCore76 (h:ℂ) (s:ℂ) := by
  norm_num [boundaryLowCore77,boundaryLowCore76] <;> push_cast <;> ring

def boundaryR77 (h s : ℝ) : ℝ := s*(1-h^2*(1/12-7*h/72)*s)
def boundaryZ77 (h s : ℝ) : ℝ := (1-h*(1/12-7*h/72)*s)/3
theorem boundaryR77_ofReal (h s : ℝ) :
    ((boundaryR77 h s:ℝ):ℂ)=nonlinearBoundaryR (h:ℂ) (s:ℂ) := by
  unfold boundaryR77 nonlinearBoundaryR nonlinearBoundarySeed
  push_cast
  ring
theorem boundaryZ77_ofReal (h s : ℝ) :
    ((boundaryZ77 h s:ℝ):ℂ)=nonlinearBoundaryZ (h:ℂ) (s:ℂ) := by
  unfold boundaryZ77 nonlinearBoundaryZ nonlinearBoundaryT nonlinearBoundarySeed
  push_cast
  ring

def boundaryRegularCore77 (h s : ℝ) : ℝ :=
  boundaryLowCore77 h s+boundaryReHigh77 h (boundaryR77 h s)+
    boundaryZ77 h s*boundaryImHigh77 h (boundaryR77 h s)

theorem boundaryRegularCore77_ofReal (h s : ℝ) :
    ((boundaryRegularCore77 h s:ℝ):ℂ)=boundaryRegularCore76 (h:ℂ) (s:ℂ) := by
  dsimp only [boundaryRegularCore77,boundaryRegularCore76]
  push_cast
  rw [boundaryLowCore77_ofReal,boundaryReHigh77_ofReal,boundaryImHigh77_ofReal,
    boundaryR77_ofReal,boundaryZ77_ofReal]

end
end HTGeometry.ThetaRatioInfinity
