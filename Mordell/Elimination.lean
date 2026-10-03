import Mordell.Elimination.Step13

namespace Mordell.Elimination

theorem projection (s k c B : ℂ)
    (h0 : g0 s k c B = 0)
    (h1 : g1 s k c B = 0)
    (h2 : g2 s k c B = 0)
    (h3 : g3 s k c B = 0)
    : g258 s k c B = 0 := zero258 s k c B h0 h1 h2 h3

theorem c_graph (s k c B : ℂ)
    (h0 : g0 s k c B = 0)
    (h1 : g1 s k c B = 0)
    (h2 : g2 s k c B = 0)
    (h3 : g3 s k c B = 0)
    : g259 s k c B = 0 := zero259 s k c B h0 h1 h2 h3

theorem k_graph (s k c B : ℂ)
    (h0 : g0 s k c B = 0)
    (h1 : g1 s k c B = 0)
    (h2 : g2 s k c B = 0)
    (h3 : g3 s k c B = 0)
    : g260 s k c B = 0 := zero260 s k c B h0 h1 h2 h3

end Mordell.Elimination
