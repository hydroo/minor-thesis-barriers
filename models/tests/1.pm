ctmc

const m_init = 0;
const m_1    = m_init;
const m_2    = 1;
const m_3    = 2;

module t0
    l_0 : [m_1..m_2] init m_init;

    []             l_0=m_1 -> 1 : (l_0'=m_1);
endmodule

module t1
    l_1 : [m_1..m_3] init m_init;

    []             l_1=m_1 -> 2 : (l_1'=m_3);
    []             l_1=m_3 -> 4 : (l_1'=m_1);
    []             l_1=m_1 -> 1 : (l_1'=m_2);
endmodule

rewards "time"
    true : 1;
endrewards

